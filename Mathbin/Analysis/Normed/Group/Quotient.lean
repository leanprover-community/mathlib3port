import Mathbin.Analysis.Normed.Group.Hom

/-!
# Quotients of seminormed groups

For any `semi_normed_group M` and any `S : add_subgroup M`, we provide a `semi_normed_group`
structure on `quotient_add_group.quotient S` (abreviated `quotient S` in the following).
If `S` is closed, we provide `normed_group (quotient S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `quotient S`.

This file also introduces a predicate `is_quotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.


## Main definitions


We use `M` and `N` to denote seminormed groups and `S : add_subgroup M`.
All the following definitions are in the `add_subgroup` namespace. Hence we can access
`add_subgroup.normed_mk S` as `S.normed_mk`.

* `semi_normed_group_quotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_group_quotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_mk S` : the normed group hom from `M` to `quotient S`.

* `lift S f hf`: implements the universal property of `quotient S`. Here
    `(f : normed_group_hom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : normed_group_hom (quotient S) N`.

* `is_quotient`: given `f : normed_group_hom M N`, `is_quotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normed_mk` : the operator norm of the projection is `1` if the subspace is not dense.

* `is_quotient.norm_lift`: Provided `f : normed_hom M N` satisfies `is_quotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ∥m∥ < ∥n∥ + ε`.


## Implementation details

For any `semi_normed_group M` and any `S : add_subgroup M` we define a norm on `quotient S` by
`∥x∥ = Inf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `quotient S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `semi_normed_group` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhd_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ∥x∥ < ε}` for positive `ε`.

Once this mathematical point it settled, we have two topologies that are propositionaly equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `semi_normed_group` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `topological_add_group.to_uniform_space`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/


noncomputable theory

open QuotientAddGroup Metric Set

open_locale TopologicalSpace Nnreal

variable {M N : Type _} [SemiNormedGroup M] [SemiNormedGroup N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable instance normOnQuotient (S : AddSubgroup M) : HasNorm (Quotientₓ S) :=
  { norm := fun x => Inf (norm '' { m | mk' S m = x }) }

theorem image_norm_nonempty {S : AddSubgroup M} : ∀ x : Quotientₓ S, (norm '' { m | mk' S m = x }).Nonempty :=
  by 
    rintro ⟨m⟩
    rw [Set.nonempty_image_iff]
    use m 
    change mk' S m = _ 
    rfl

theorem bdd_below_image_norm (s : Set M) : BddBelow (norm '' s) :=
  by 
    use 0
    rintro _ ⟨x, hx, rfl⟩
    apply norm_nonneg

/-- The norm on the quotient satisfies `∥-x∥ = ∥x∥`. -/
theorem quotient_norm_neg {S : AddSubgroup M} (x : Quotientₓ S) : ∥-x∥ = ∥x∥ :=
  by 
    suffices  : norm '' { m | mk' S m = x } = norm '' { m | mk' S m = -x }
    ·
      simp only [this, norm]
    ext r 
    split 
    ·
      rintro ⟨m, hm : mk' S m = x, rfl⟩
      subst hm 
      rw [←norm_neg]
      exact
        ⟨-m,
          by 
            simp only [(mk' S).map_neg, Set.mem_set_of_eq],
          rfl⟩
    ·
      rintro ⟨m, hm : mk' S m = -x, rfl⟩
      use -m 
      simp  at hm 
      simp [hm]

theorem quotient_norm_sub_rev {S : AddSubgroup M} (x y : Quotientₓ S) : ∥x - y∥ = ∥y - x∥ :=
  by 
    rw
      [show x - y = -(y - x)by 
        abel,
      quotient_norm_neg]

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le (S : AddSubgroup M) (m : M) : ∥mk' S m∥ ≤ ∥m∥ :=
  by 
    apply cInf_le 
    use 0
    ·
      rintro _ ⟨n, h, rfl⟩
      apply norm_nonneg
    ·
      apply Set.mem_image_of_mem 
      rw [Set.mem_set_of_eq]

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le' (S : AddSubgroup M) (m : M) : ∥(m : Quotientₓ S)∥ ≤ ∥m∥ :=
  quotient_norm_mk_le S m

/-- The norm of the image under the natural morphism to the quotient. -/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) : ∥mk' S m∥ = Inf ((fun x => ∥m+x∥) '' S) :=
  by 
    change Inf _ = _ 
    congr 1 
    ext r 
    simpRw [coe_mk', eq_iff_sub_mem]
    split 
    ·
      rintro ⟨y, h, rfl⟩
      use y - m, h 
      simp 
    ·
      rintro ⟨y, h, rfl⟩
      use m+y 
      simpa using h

/-- The quotient norm is nonnegative. -/
theorem quotient_norm_nonneg (S : AddSubgroup M) : ∀ x : Quotientₓ S, 0 ≤ ∥x∥ :=
  by 
    rintro ⟨m⟩
    change 0 ≤ ∥mk' S m∥
    apply le_cInf (image_norm_nonempty _)
    rintro _ ⟨n, h, rfl⟩
    apply norm_nonneg

/-- The quotient norm is nonnegative. -/
theorem norm_mk_nonneg (S : AddSubgroup M) (m : M) : 0 ≤ ∥mk' S m∥ :=
  quotient_norm_nonneg S _

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
theorem quotient_norm_eq_zero_iff
(S : add_subgroup M)
(m : M) : «expr ↔ »(«expr = »(«expr∥ ∥»(mk' S m), 0), «expr ∈ »(m, closure (S : set M))) :=
begin
  have [] [":", expr «expr ≤ »(0, «expr∥ ∥»(mk' S m))] [":=", expr norm_mk_nonneg S m],
  rw ["[", "<-", expr this.le_iff_eq, ",", expr quotient_norm_mk_eq, ",", expr real.Inf_le_iff, "]"] [],
  simp_rw ["[", expr zero_add, "]"] [],
  { calc
      «expr ↔ »(∀
       ε «expr > » (0 : exprℝ()), «expr∃ , »((r «expr ∈ » «expr '' »(λ
          x, «expr∥ ∥»(«expr + »(m, x)), (S : set M))), «expr < »(r, ε)), ∀
       ε «expr > » 0, «expr∃ , »((x «expr ∈ » S), «expr < »(«expr∥ ∥»(«expr + »(m, x)), ε))) : by simp [] [] [] ["[", expr set.bex_image_iff, "]"] [] []
      «expr ↔ »(..., ∀
       ε «expr > » 0, «expr∃ , »((x «expr ∈ » S), «expr < »(«expr∥ ∥»(«expr + »(m, «expr- »(x))), ε))) : _
      «expr ↔ »(..., ∀
       ε «expr > » 0, «expr∃ , »((x «expr ∈ » S), «expr ∈ »(x, metric.ball m ε))) : by simp [] [] [] ["[", expr dist_eq_norm, ",", "<-", expr sub_eq_add_neg, ",", expr norm_sub_rev, "]"] [] []
      «expr ↔ »(..., «expr ∈ »(m, closure «expr↑ »(S))) : by simp [] [] [] ["[", expr metric.mem_closure_iff, ",", expr dist_comm, "]"] [] [],
    apply [expr forall_congr],
    intro [ident ε],
    apply [expr forall_congr],
    intro [ident ε_pos],
    rw ["[", "<-", expr S.exists_neg_mem_iff_exists_mem, "]"] [],
    simp [] [] [] [] [] [] },
  { use [expr 0],
    rintro ["_", "⟨", ident x, ",", ident x_in, ",", ident rfl, "⟩"],
    apply [expr norm_nonneg] },
  rw [expr set.nonempty_image_iff] [],
  use ["[", expr 0, ",", expr S.zero_mem, "]"]
end

/-- For any `x : quotient S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `∥m∥ < ∥x∥ + ε`. -/
theorem norm_mk_lt {S : AddSubgroup M} (x : Quotientₓ S) {ε : ℝ} (hε : 0 < ε) : ∃ m : M, mk' S m = x ∧ ∥m∥ < ∥x∥+ε :=
  by 
    obtain ⟨_, ⟨m : M, H : mk' S m = x, rfl⟩, hnorm : ∥m∥ < ∥x∥+ε⟩ := Real.lt_Inf_add_pos (image_norm_nonempty x) hε 
    subst H 
    exact ⟨m, rfl, hnorm⟩

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `∥m + s∥ < ∥mk' S m∥ + ε`. -/
theorem norm_mk_lt' (S : AddSubgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) : ∃ (s : _)(_ : s ∈ S), ∥m+s∥ < ∥mk' S m∥+ε :=
  by 
    obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ∥n∥ < ∥mk' S m∥+ε⟩ := norm_mk_lt (QuotientAddGroup.mk' S m) hε 
    erw [eq_comm, QuotientAddGroup.eq] at hn 
    use (-m)+n, hn 
    rwa [add_neg_cancel_left]

/-- The quotient norm satisfies the triangle inequality. -/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : Quotientₓ S) : ∥x+y∥ ≤ ∥x∥+∥y∥ :=
  by 
    refine' le_of_forall_pos_le_add fun ε hε => _ 
    replace hε := half_pos hε 
    obtain ⟨m, rfl, hm : ∥m∥ < ∥mk' S m∥+ε / 2⟩ := norm_mk_lt x hε 
    obtain ⟨n, rfl, hn : ∥n∥ < ∥mk' S n∥+ε / 2⟩ := norm_mk_lt y hε 
    calc ∥mk' S m+mk' S n∥ = ∥mk' S (m+n)∥ :=
      by 
        rw [(mk' S).map_add]_ ≤ ∥m+n∥ :=
      quotient_norm_mk_le S (m+n)_ ≤ ∥m∥+∥n∥ := norm_add_le _ _ _ ≤ (∥mk' S m∥+∥mk' S n∥)+ε :=
      by 
        linarith

/-- The quotient norm of `0` is `0`. -/
theorem norm_mk_zero (S : AddSubgroup M) : ∥(0 : Quotientₓ S)∥ = 0 :=
  by 
    erw [quotient_norm_eq_zero_iff]
    exact subset_closure S.zero_mem

/-- If `(m : M)` has norm equal to `0` in `quotient S` for a closed subgroup `S` of `M`, then
`m ∈ S`. -/
theorem norm_zero_eq_zero (S : AddSubgroup M) (hS : IsClosed (S : Set M)) (m : M) (h : ∥mk' S m∥ = 0) : m ∈ S :=
  by 
    rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem quotient_nhd_basis
(S : add_subgroup M) : (expr𝓝() (0 : quotient S)).has_basis (λ
 ε : exprℝ(), «expr < »(0, ε)) (λ ε, {x | «expr < »(«expr∥ ∥»(x), ε)}) :=
⟨begin
   intros [ident U],
   split,
   { intros [ident U_in],
     rw ["<-", expr (mk' S).map_zero] ["at", ident U_in],
     have [] [] [":=", expr preimage_nhds_coinduced U_in],
     rcases [expr metric.mem_nhds_iff.mp this, "with", "⟨", ident ε, ",", ident ε_pos, ",", ident H, "⟩"],
     use ["[", expr «expr / »(ε, 2), ",", expr half_pos ε_pos, "]"],
     intros [ident x, ident x_in],
     dsimp [] [] [] ["at", ident x_in],
     rcases [expr norm_mk_lt x (half_pos ε_pos), "with", "⟨", ident y, ",", ident rfl, ",", ident ry, "⟩"],
     apply [expr H],
     rw [expr ball_zero_eq] [],
     dsimp [] [] [] [],
     linarith [] [] [] },
   { rintros ["⟨", ident ε, ",", ident ε_pos, ",", ident h, "⟩"],
     have [] [":", expr «expr ⊆ »(«expr '' »(mk' S, ball (0 : M) ε), {x | «expr < »(«expr∥ ∥»(x), ε)})] [],
     { rintros ["-", "⟨", ident x, ",", ident x_in, ",", ident rfl, "⟩"],
       rw [expr mem_ball_zero_iff] ["at", ident x_in],
       exact [expr lt_of_le_of_lt (quotient_norm_mk_le S x) x_in] },
     apply [expr filter.mem_of_superset _ (set.subset.trans this h)],
     clear [ident h, ident U, ident this],
     apply [expr is_open.mem_nhds],
     { change [expr is_open «expr ⁻¹' »(mk' S, _)] [] [],
       erw [expr quotient_add_group.preimage_image_coe] [],
       apply [expr is_open_Union],
       rintros ["⟨", ident s, ",", ident s_in, "⟩"],
       exact [expr (continuous_add_right s).is_open_preimage _ is_open_ball] },
     { exact [expr ⟨(0 : M), mem_ball_self ε_pos, (mk' S).map_zero⟩] } }
 end⟩

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The seminormed group structure on the quotient by an additive subgroup. -/
noncomputable
instance add_subgroup.semi_normed_group_quotient (S : add_subgroup M) : semi_normed_group (quotient S) :=
{ dist := λ x y, «expr∥ ∥»(«expr - »(x, y)),
  dist_self := λ x, by simp [] [] ["only"] ["[", expr norm_mk_zero, ",", expr sub_self, "]"] [] [],
  dist_comm := quotient_norm_sub_rev,
  dist_triangle := λ x y z, begin
    unfold [ident dist] [],
    have [] [":", expr «expr = »(«expr - »(x, z), «expr + »(«expr - »(x, y), «expr - »(y, z)))] [":=", expr by abel [] [] []],
    rw [expr this] [],
    exact [expr quotient_norm_add_le S «expr - »(x, y) «expr - »(y, z)]
  end,
  dist_eq := λ x y, rfl,
  to_uniform_space := topological_add_group.to_uniform_space (quotient S),
  uniformity_dist := begin
    rw [expr uniformity_eq_comap_nhds_zero'] [],
    have [] [] [":=", expr (quotient_nhd_basis S).comap (λ p : «expr × »(quotient S, quotient S), «expr - »(p.2, p.1))],
    apply [expr this.eq_of_same_basis],
    have [] [":", expr ∀
     ε : exprℝ(), «expr = »(«expr ⁻¹' »(λ
       p : «expr × »(quotient S, quotient S), «expr - »(p.snd, p.fst), {x | «expr < »(«expr∥ ∥»(x), ε)}), {p : «expr × »(quotient S, quotient S) | «expr < »(«expr∥ ∥»(«expr - »(p.fst, p.snd)), ε)})] [],
    { intro [ident ε],
      ext [] [ident x] [],
      dsimp [] [] [] [],
      rw [expr quotient_norm_sub_rev] [] },
    rw [expr funext this] [],
    refine [expr filter.has_basis_binfi_principal _ set.nonempty_Ioi],
    rintros [ident ε, "(", ident ε_pos, ":", expr «expr < »(0, ε), ")", ident η, "(", ident η_pos, ":", expr «expr < »(0, η), ")"],
    refine [expr ⟨min ε η, lt_min ε_pos η_pos, _, _⟩],
    { suffices [] [":", expr ∀
       a
       b : quotient S, «expr < »(«expr∥ ∥»(«expr - »(a, b)), ε) → «expr < »(«expr∥ ∥»(«expr - »(a, b)), η) → «expr < »(«expr∥ ∥»(«expr - »(a, b)), ε)],
      by simpa [] [] [] [] [] [],
      exact [expr λ a b h h', h] },
    { simp [] [] [] [] [] [] }
  end }

example (S : AddSubgroup M) :
  (Quotientₓ.topologicalSpace : TopologicalSpace$ Quotientₓ S) =
    S.semi_normed_group_quotient.to_uniform_space.to_topological_space :=
  rfl

/-- The quotient in the category of normed groups. -/
noncomputable instance AddSubgroup.normedGroupQuotient (S : AddSubgroup M) [hS : IsClosed (S : Set M)] :
  NormedGroup (Quotientₓ S) :=
  { AddSubgroup.semiNormedGroupQuotient S with
    eq_of_dist_eq_zero :=
      by 
        rintro ⟨m⟩ ⟨m'⟩ (h : ∥mk' S m - mk' S m'∥ = 0)
        erw [←(mk' S).map_sub, quotient_norm_eq_zero_iff, hS.closure_eq, ←QuotientAddGroup.eq_iff_sub_mem] at h 
        exact h }

example (S : AddSubgroup M) [IsClosed (S : Set M)] : S.semi_normed_group_quotient = NormedGroup.toSemiNormedGroup :=
  rfl

namespace AddSubgroup

open NormedGroupHom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
noncomputable def normed_mk (S : AddSubgroup M) : NormedGroupHom M (Quotientₓ S) :=
  { QuotientAddGroup.mk' S with
    bound' :=
      ⟨1,
        fun m =>
          by 
            simpa [one_mulₓ] using quotient_norm_mk_le _ m⟩ }

/-- `S.normed_mk` agrees with `quotient_add_group.mk' S`. -/
@[simp]
theorem normed_mk.apply (S : AddSubgroup M) (m : M) : normed_mk S m = QuotientAddGroup.mk' S m :=
  rfl

/-- `S.normed_mk` is surjective. -/
theorem surjective_normed_mk (S : AddSubgroup M) : Function.Surjective (normed_mk S) :=
  surjective_quot_mk _

/-- The kernel of `S.normed_mk` is `S`. -/
theorem ker_normed_mk (S : AddSubgroup M) : S.normed_mk.ker = S :=
  QuotientAddGroup.ker_mk _

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normed_mk_le (S : AddSubgroup M) : ∥S.normed_mk∥ ≤ 1 :=
  NormedGroupHom.op_norm_le_bound _ zero_le_one
    fun m =>
      by 
        simp [quotient_norm_mk_le']

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The operator norm of the projection is `1` if the subspace is not dense. -/
theorem norm_normed_mk
(S : add_subgroup M)
(h : «expr ≠ »((S.topological_closure : set M), univ)) : «expr = »(«expr∥ ∥»(S.normed_mk), 1) :=
begin
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":=", expr set.nonempty_compl.2 h],
  let [ident y] [] [":=", expr S.normed_mk x],
  have [ident hy] [":", expr «expr ≠ »(«expr∥ ∥»(y), 0)] [],
  { intro [ident h0],
    exact [expr set.not_mem_of_mem_compl hx ((quotient_norm_eq_zero_iff S x).1 h0)] },
  refine [expr le_antisymm (norm_normed_mk_le S) (le_of_forall_pos_le_add (λ ε hε, _))],
  suffices [] [":", expr «expr ≤ »(1, «expr + »(«expr∥ ∥»(S.normed_mk), min ε «expr / »((1 : exprℝ()), 2)))],
  { exact [expr le_add_of_le_add_left this (min_le_left ε «expr / »((1 : exprℝ()), 2))] },
  have [ident hδ] [] [":=", expr sub_pos.mpr (lt_of_le_of_lt (min_le_right ε «expr / »((1 : exprℝ()), 2)) one_half_lt_one)],
  have [ident hδpos] [":", expr «expr < »(0, min ε «expr / »((1 : exprℝ()), 2))] [":=", expr lt_min hε one_half_pos],
  have [ident hδnorm] [] [":=", expr mul_pos (div_pos hδpos hδ) (lt_of_le_of_ne (norm_nonneg y) hy.symm)],
  obtain ["⟨", ident m, ",", ident hm, ",", ident hlt, "⟩", ":=", expr norm_mk_lt y hδnorm],
  have [ident hrw] [":", expr «expr = »(«expr + »(«expr∥ ∥»(y), «expr * »(«expr / »(min ε «expr / »(1, 2), «expr - »(1, min ε «expr / »(1, 2))), «expr∥ ∥»(y))), «expr * »(«expr∥ ∥»(y), «expr + »(1, «expr / »(min ε «expr / »(1, 2), «expr - »(1, min ε «expr / »(1, 2))))))] [":=", expr by ring []],
  rw ["[", expr hrw, "]"] ["at", ident hlt],
  have [ident hm0] [":", expr «expr ≠ »(«expr∥ ∥»(m), 0)] [],
  { intro [ident h0],
    have [ident hnorm] [] [":=", expr quotient_norm_mk_le S m],
    rw ["[", expr h0, ",", expr hm, "]"] ["at", ident hnorm],
    replace [ident hnorm] [] [":=", expr le_antisymm hnorm (norm_nonneg _)],
    simpa [] [] [] ["[", expr hnorm, "]"] [] ["using", expr hy] },
  replace [ident hlt] [] [":=", expr (div_lt_div_right (lt_of_le_of_ne (norm_nonneg m) hm0.symm)).2 hlt],
  simp [] [] ["only"] ["[", expr hm0, ",", expr div_self, ",", expr ne.def, ",", expr not_false_iff, "]"] [] ["at", ident hlt],
  have [ident hrw₁] [":", expr «expr = »(«expr / »(«expr * »(«expr∥ ∥»(y), «expr + »(1, «expr / »(min ε «expr / »(1, 2), «expr - »(1, min ε «expr / »(1, 2))))), «expr∥ ∥»(m)), «expr * »(«expr / »(«expr∥ ∥»(y), «expr∥ ∥»(m)), «expr + »(1, «expr / »(min ε «expr / »(1, 2), «expr - »(1, min ε «expr / »(1, 2))))))] [":=", expr by ring []],
  rw ["[", expr hrw₁, "]"] ["at", ident hlt],
  replace [ident hlt] [] [":=", expr (inv_pos_lt_iff_one_lt_mul (lt_trans (div_pos hδpos hδ) (lt_one_add _))).2 hlt],
  suffices [] [":", expr «expr ≥ »(«expr∥ ∥»(S.normed_mk), «expr - »(1, min ε «expr / »(1, 2)))],
  { exact [expr sub_le_iff_le_add.mp this] },
  calc
    «expr ≥ »(«expr∥ ∥»(S.normed_mk), «expr / »(«expr∥ ∥»(S.normed_mk m), «expr∥ ∥»(m))) : ratio_le_op_norm S.normed_mk m
    «expr = »(..., «expr / »(«expr∥ ∥»(y), «expr∥ ∥»(m))) : by rw ["[", expr normed_mk.apply, ",", expr hm, "]"] []
    «expr ≥ »(..., «expr ⁻¹»(«expr + »(1, «expr / »(min ε «expr / »(1, 2), «expr - »(1, min ε «expr / »(1, 2)))))) : le_of_lt hlt
    «expr = »(..., «expr - »(1, min ε «expr / »(1, 2))) : by field_simp [] ["[", expr (ne_of_lt hδ).symm, "]"] [] []
end

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The operator norm of the projection is `0` if the subspace is dense. -/
theorem norm_trivial_quotient_mk
(S : add_subgroup M)
(h : «expr = »((S.topological_closure : set M), set.univ)) : «expr = »(«expr∥ ∥»(S.normed_mk), 0) :=
begin
  refine [expr le_antisymm (op_norm_le_bound _ (le_refl _) (λ x, _)) (norm_nonneg _)],
  have [ident hker] [":", expr «expr ∈ »(x, S.normed_mk.ker.topological_closure)] [],
  { rw ["[", expr S.ker_normed_mk, "]"] [],
    exact [expr set.mem_of_eq_of_mem h trivial] },
  rw ["[", expr ker_normed_mk, "]"] ["at", ident hker],
  simp [] [] ["only"] ["[", expr (quotient_norm_eq_zero_iff S x).mpr hker, ",", expr normed_mk.apply, ",", expr zero_mul, "]"] [] []
end

end AddSubgroup

namespace NormedGroupHom

/-- `is_quotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure is_quotient (f : NormedGroupHom M N) : Prop where 
  Surjective : Function.Surjective f 
  norm : ∀ x, ∥f x∥ = Inf ((fun m => ∥x+m∥) '' f.ker)

/-- Given  `f : normed_group_hom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : add_subgroup M` is closed, the induced morphism `normed_group_hom (quotient S) N`. -/
noncomputable def lift {N : Type _} [SemiNormedGroup N] (S : AddSubgroup M) (f : NormedGroupHom M N)
  (hf : ∀ s _ : s ∈ S, f s = 0) : NormedGroupHom (Quotientₓ S) N :=
  { QuotientAddGroup.lift S f.to_add_monoid_hom hf with
    bound' :=
      by 
        obtain ⟨c : ℝ, hcpos : (0 : ℝ) < c, hc : ∀ x, ∥f x∥ ≤ c*∥x∥⟩ := f.bound 
        refine' ⟨c, fun mbar => le_of_forall_pos_le_add fun ε hε => _⟩
        obtain ⟨m : M, rfl : mk' S m = mbar, hmnorm : ∥m∥ < ∥mk' S m∥+ε / c⟩ := norm_mk_lt mbar (div_pos hε hcpos)
        calc ∥f m∥ ≤ c*∥m∥ := hc m _ ≤ c*∥mk' S m∥+ε / c :=
          ((mul_lt_mul_left hcpos).mpr hmnorm).le _ = (c*∥mk' S m∥)+ε :=
          by 
            rw [mul_addₓ, mul_div_cancel' _ hcpos.ne.symm] }

theorem lift_mk {N : Type _} [SemiNormedGroup N] (S : AddSubgroup M) (f : NormedGroupHom M N)
  (hf : ∀ s _ : s ∈ S, f s = 0) (m : M) : lift S f hf (S.normed_mk m) = f m :=
  rfl

theorem lift_unique {N : Type _} [SemiNormedGroup N] (S : AddSubgroup M) (f : NormedGroupHom M N)
  (hf : ∀ s _ : s ∈ S, f s = 0) (g : NormedGroupHom (Quotientₓ S) N) : g.comp S.normed_mk = f → g = lift S f hf :=
  by 
    intro h 
    ext 
    rcases AddSubgroup.surjective_normed_mk _ x with ⟨x, rfl⟩
    change g.comp S.normed_mk x = _ 
    simpa only [h]

/-- `S.normed_mk` satisfies `is_quotient`. -/
theorem is_quotient_quotient (S : AddSubgroup M) : is_quotient S.normed_mk :=
  ⟨S.surjective_normed_mk,
    fun m =>
      by 
        simpa [S.ker_normed_mk] using quotient_norm_mk_eq _ m⟩

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_quotient.norm_lift
{f : normed_group_hom M N}
(hquot : is_quotient f)
{ε : exprℝ()}
(hε : «expr < »(0, ε))
(n : N) : «expr∃ , »((m : M), «expr ∧ »(«expr = »(f m, n), «expr < »(«expr∥ ∥»(m), «expr + »(«expr∥ ∥»(n), ε)))) :=
begin
  obtain ["⟨", ident m, ",", ident rfl, "⟩", ":=", expr hquot.surjective n],
  have [ident nonemp] [":", expr «expr '' »(λ m', «expr∥ ∥»(«expr + »(m, m')), f.ker).nonempty] [],
  { rw [expr set.nonempty_image_iff] [],
    exact [expr ⟨0, f.ker.zero_mem⟩] },
  rcases [expr real.lt_Inf_add_pos nonemp hε, "with", "⟨", "_", ",", "⟨", "⟨", ident x, ",", ident hx, ",", ident rfl, "⟩", ",", ident H, ":", expr «expr < »(«expr∥ ∥»(«expr + »(m, x)), «expr + »(Inf «expr '' »(λ
      m' : M, «expr∥ ∥»(«expr + »(m, m')), f.ker), ε)), "⟩", "⟩"],
  exact [expr ⟨«expr + »(m, x), by rw ["[", expr f.map_add, ",", expr (normed_group_hom.mem_ker f x).mp hx, ",", expr add_zero, "]"] [], by rwa [expr hquot.norm] []⟩]
end

theorem is_quotient.norm_le {f : NormedGroupHom M N} (hquot : is_quotient f) (m : M) : ∥f m∥ ≤ ∥m∥ :=
  by 
    rw [hquot.norm]
    apply cInf_le
    ·
      use 0
      rintro _ ⟨m', hm', rfl⟩
      apply norm_nonneg
    ·
      exact
        ⟨0, f.ker.zero_mem,
          by 
            simp ⟩

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_norm_le
{N : Type*}
[semi_normed_group N]
(S : add_subgroup M)
(f : normed_group_hom M N)
(hf : ∀ s «expr ∈ » S, «expr = »(f s, 0))
{c : «exprℝ≥0»()}
(fb : «expr ≤ »(«expr∥ ∥»(f), c)) : «expr ≤ »(«expr∥ ∥»(lift S f hf), c) :=
begin
  apply [expr op_norm_le_bound _ c.coe_nonneg],
  intros [ident x],
  by_cases [expr hc, ":", expr «expr = »(c, 0)],
  { simp [] [] ["only"] ["[", expr hc, ",", expr nnreal.coe_zero, ",", expr zero_mul, "]"] [] ["at", ident fb, "⊢"],
    obtain ["⟨", ident x, ",", ident rfl, "⟩", ":=", expr surjective_quot_mk _ x],
    show [expr «expr ≤ »(«expr∥ ∥»(f x), 0)],
    calc
      «expr ≤ »(«expr∥ ∥»(f x), «expr * »(0, «expr∥ ∥»(x))) : f.le_of_op_norm_le fb x
      «expr = »(..., 0) : zero_mul _ },
  { replace [ident hc] [":", expr «expr < »(0, c)] [":=", expr pos_iff_ne_zero.mpr hc],
    apply [expr le_of_forall_pos_le_add],
    intros [ident ε, ident hε],
    have [ident aux] [":", expr «expr < »(0, «expr / »(ε, c))] [":=", expr div_pos hε hc],
    obtain ["⟨", ident x, ",", ident rfl, ",", ident Hx, "⟩", ":", expr «expr∃ , »((x'), «expr ∧ »(«expr = »(S.normed_mk x', x), «expr < »(«expr∥ ∥»(x'), «expr + »(«expr∥ ∥»(x), «expr / »(ε, c))))), ":=", expr (is_quotient_quotient _).norm_lift aux _],
    rw [expr lift_mk] [],
    calc
      «expr ≤ »(«expr∥ ∥»(f x), «expr * »(c, «expr∥ ∥»(x))) : f.le_of_op_norm_le fb x
      «expr ≤ »(..., «expr * »(c, «expr + »(«expr∥ ∥»(S.normed_mk x), «expr / »(ε, c)))) : (mul_le_mul_left _).mpr Hx.le
      «expr = »(..., «expr + »(«expr * »(c, _), ε)) : _,
    { exact_mod_cast [expr hc] },
    { rw ["[", expr mul_add, ",", expr mul_div_cancel', "]"] [],
      exact_mod_cast [expr hc.ne'] } }
end

-- error in Analysis.Normed.Group.Quotient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_norm_noninc
{N : Type*}
[semi_normed_group N]
(S : add_subgroup M)
(f : normed_group_hom M N)
(hf : ∀ s «expr ∈ » S, «expr = »(f s, 0))
(fb : f.norm_noninc) : (lift S f hf).norm_noninc :=
λ x, begin
  have [ident fb'] [":", expr «expr ≤ »(«expr∥ ∥»(f), (1 : «exprℝ≥0»()))] [":=", expr norm_noninc.norm_noninc_iff_norm_le_one.mp fb],
  simpa [] [] [] [] [] ["using", expr le_of_op_norm_le _ (f.lift_norm_le _ _ fb') _]
end

end NormedGroupHom

