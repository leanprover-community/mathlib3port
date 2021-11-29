import Mathbin.LinearAlgebra.AffineSpace.Independent 
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/


noncomputable theory

open_locale BigOperators Classical Affine

section AffineSpace'

variable (k : Type _) {V : Type _} {P : Type _} [Field k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

variable {ι : Type _}

include V

open AffineSubspace FiniteDimensional Module

/-- The `vector_span` of a finite set is finite-dimensional. -/
theorem finite_dimensional_vector_span_of_finite {s : Set P} (h : Set.Finite s) :
  FiniteDimensional k (vectorSpan k s) :=
  span_of_finite k$ h.vsub h

/-- The `vector_span` of a family indexed by a `fintype` is
finite-dimensional. -/
instance finite_dimensional_vector_span_of_fintype [Fintype ι] (p : ι → P) :
  FiniteDimensional k (vectorSpan k (Set.Range p)) :=
  finite_dimensional_vector_span_of_finite k (Set.finite_range _)

/-- The `vector_span` of a subset of a family indexed by a `fintype`
is finite-dimensional. -/
instance finite_dimensional_vector_span_image_of_fintype [Fintype ι] (p : ι → P) (s : Set ι) :
  FiniteDimensional k (vectorSpan k (p '' s)) :=
  finite_dimensional_vector_span_of_finite k ((Set.Finite.of_fintype _).Image _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
theorem finite_dimensional_direction_affine_span_of_finite {s : Set P} (h : Set.Finite s) :
  FiniteDimensional k (affineSpan k s).direction :=
  (direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [Fintype ι] (p : ι → P) :
  FiniteDimensional k (affineSpan k (Set.Range p)).direction :=
  finite_dimensional_direction_affine_span_of_finite k (Set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [Fintype ι] (p : ι → P) (s : Set ι) :
  FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finite_dimensional_direction_affine_span_of_finite k ((Set.Finite.of_fintype _).Image _)

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
noncomputable
def fintype_of_fin_dim_affine_independent
[finite_dimensional k V]
{p : ι → P}
(hi : affine_independent k p) : fintype ι :=
if hι : is_empty ι then @fintype.of_is_empty _ hι else begin
  let [ident q] [] [":=", expr (not_is_empty_iff.mp hι).some],
  rw [expr affine_independent_iff_linear_independent_vsub k p q] ["at", ident hi],
  letI [] [":", expr is_noetherian k V] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  exact [expr fintype_of_fintype_ne _ (fintype_of_is_noetherian_linear_independent hi)]
end

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
theorem finite_of_fin_dim_affine_independent [FiniteDimensional k V] {s : Set P}
  (hi : AffineIndependent k (coeₓ : s → P)) : s.finite :=
  ⟨fintypeOfFinDimAffineIndependent k hi⟩

variable {k}

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `vector_span` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
theorem affine_independent.finrank_vector_span_image_finset
{p : ι → P}
(hi : affine_independent k p)
{s : finset ι}
{n : exprℕ()}
(hc : «expr = »(finset.card s, «expr + »(n, 1))) : «expr = »(finrank k (vector_span k (s.image p : set P)), n) :=
begin
  have [ident hi'] [] [":=", expr hi.range.mono (set.image_subset_range p «expr↑ »(s))],
  have [ident hc'] [":", expr «expr = »((s.image p).card, «expr + »(n, 1))] [],
  { rwa [expr s.card_image_of_injective hi.injective] [] },
  have [ident hn] [":", expr (s.image p).nonempty] [],
  { simp [] [] [] ["[", expr hc', ",", "<-", expr finset.card_pos, "]"] [] [] },
  rcases [expr hn, "with", "⟨", ident p₁, ",", ident hp₁, "⟩"],
  have [ident hp₁'] [":", expr «expr ∈ »(p₁, «expr '' »(p, s))] [":=", expr by simpa [] [] [] [] [] ["using", expr hp₁]],
  rw ["[", expr affine_independent_set_iff_linear_independent_vsub k hp₁', ",", "<-", expr finset.coe_singleton, ",", "<-", expr finset.coe_image, ",", "<-", expr finset.coe_sdiff, ",", expr finset.sdiff_singleton_eq_erase, ",", "<-", expr finset.coe_image, "]"] ["at", ident hi'],
  have [ident hc] [":", expr «expr = »((finset.image (λ
      p : P, «expr -ᵥ »(p, p₁)) ((finset.image p s).erase p₁)).card, n)] [],
  { rw ["[", expr finset.card_image_of_injective _ (vsub_left_injective _), ",", expr finset.card_erase_of_mem hp₁, "]"] [],
    exact [expr nat.pred_eq_of_eq_succ hc'] },
  rwa ["[", expr vector_span_eq_span_vsub_finset_right_ne k hp₁, ",", expr finrank_span_finset_eq_card, ",", expr hc, "]"] []
end

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
theorem AffineIndependent.finrank_vector_span [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) {n : ℕ}
  (hc : Fintype.card ι = n+1) : finrank k (vectorSpan k (Set.Range p)) = n :=
  by 
    rw [←Finset.card_univ] at hc 
    rw [←Set.image_univ, ←Finset.coe_univ, ←Finset.coe_image]
    exact hi.finrank_vector_span_image_finset hc

/-- If the `vector_span` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one {p : ι → P}
  (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
  (hle : vectorSpan k (s.image p : Set P) ≤ sm) (hc : Finset.card s = finrank k sm+1) :
  vectorSpan k (s.image p : Set P) = sm :=
  eq_of_le_of_finrank_eq hle$ hi.finrank_vector_span_image_finset hc

/-- If the `vector_span` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
theorem AffineIndependent.vector_span_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
  (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm] (hle : vectorSpan k (Set.Range p) ≤ sm)
  (hc : Fintype.card ι = finrank k sm+1) : vectorSpan k (Set.Range p) = sm :=
  eq_of_le_of_finrank_eq hle$ hi.finrank_vector_span hc

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the `affine_span` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
theorem affine_independent.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one
{p : ι → P}
(hi : affine_independent k p)
{s : finset ι}
{sp : affine_subspace k P}
[finite_dimensional k sp.direction]
(hle : «expr ≤ »(affine_span k (s.image p : set P), sp))
(hc : «expr = »(finset.card s, «expr + »(finrank k sp.direction, 1))) : «expr = »(affine_span k (s.image p : set P), sp) :=
begin
  have [ident hn] [":", expr (s.image p).nonempty] [],
  { rw ["[", expr finset.nonempty.image_iff, ",", "<-", expr finset.card_pos, ",", expr hc, "]"] [],
    apply [expr nat.succ_pos] },
  refine [expr eq_of_direction_eq_of_nonempty_of_le _ ((affine_span_nonempty k _).2 hn) hle],
  have [ident hd] [] [":=", expr direction_le hle],
  rw [expr direction_affine_span] ["at", "⊢", ident hd],
  exact [expr hi.vector_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc]
end

/-- If the `affine_span` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
theorem AffineIndependent.affine_span_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
  (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
  (hle : affineSpan k (Set.Range p) ≤ sp) (hc : Fintype.card ι = finrank k sp.direction+1) :
  affineSpan k (Set.Range p) = sp :=
  by 
    rw [←Finset.card_univ] at hc 
    rw [←Set.image_univ, ←Finset.coe_univ, ←Finset.coe_image] at hle⊢
    exact hi.affine_span_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
theorem AffineIndependent.vector_span_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V] [Fintype ι] {p : ι → P}
  (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V+1) : vectorSpan k (Set.Range p) = ⊤ :=
  eq_top_of_finrank_eq$ hi.finrank_vector_span hc

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `affine_span` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
theorem affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one
[finite_dimensional k V]
[fintype ι]
{p : ι → P}
(hi : affine_independent k p) : «expr ↔ »(«expr = »(affine_span k (set.range p), «expr⊤»()), «expr = »(fintype.card ι, «expr + »(finrank k V, 1))) :=
begin
  split,
  { intros [ident h_tot],
    let [ident n] [] [":=", expr «expr - »(fintype.card ι, 1)],
    have [ident hn] [":", expr «expr = »(fintype.card ι, «expr + »(n, 1))] [],
    { exact [expr (nat.succ_pred_eq_of_pos (card_pos_of_affine_span_eq_top k V P h_tot)).symm] },
    rw ["[", expr hn, ",", "<-", expr finrank_top, ",", "<-", expr vector_span_eq_top_of_affine_span_eq_top k V P h_tot, ",", "<-", expr hi.finrank_vector_span hn, "]"] [] },
  { intros [ident hc],
    rw ["[", "<-", expr finrank_top, ",", "<-", expr direction_top k V P, "]"] ["at", ident hc],
    exact [expr hi.affine_span_eq_of_le_of_card_eq_finrank_add_one le_top hc] }
end

variable (k)

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `vector_span` of `n + 1` points in an indexed family has
dimension at most `n`. -/
theorem finrank_vector_span_image_finset_le
(p : ι → P)
(s : finset ι)
{n : exprℕ()}
(hc : «expr = »(finset.card s, «expr + »(n, 1))) : «expr ≤ »(finrank k (vector_span k (s.image p : set P)), n) :=
begin
  have [ident hn] [":", expr (s.image p).nonempty] [],
  { rw ["[", expr finset.nonempty.image_iff, ",", "<-", expr finset.card_pos, ",", expr hc, "]"] [],
    apply [expr nat.succ_pos] },
  rcases [expr hn, "with", "⟨", ident p₁, ",", ident hp₁, "⟩"],
  rw ["[", expr vector_span_eq_span_vsub_finset_right_ne k hp₁, "]"] [],
  refine [expr le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image (λ p, «expr -ᵥ »(p, p₁)))) _],
  rw ["[", expr finset.card_image_of_injective _ (vsub_left_injective p₁), ",", expr finset.card_erase_of_mem hp₁, ",", expr nat.pred_le_iff, ",", expr nat.succ_eq_add_one, ",", "<-", expr hc, "]"] [],
  apply [expr finset.card_image_le]
end

/-- The `vector_span` of an indexed family of `n + 1` points has
dimension at most `n`. -/
theorem finrank_vector_span_range_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n+1) :
  finrank k (vectorSpan k (Set.Range p)) ≤ n :=
  by 
    rw [←Set.image_univ, ←Finset.coe_univ, ←Finset.coe_image]
    rw [←Finset.card_univ] at hc 
    exact finrank_vector_span_image_finset_le _ _ _ hc

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension `n`. -/
theorem affine_independent_iff_finrank_vector_span_eq
[fintype ι]
(p : ι → P)
{n : exprℕ()}
(hc : «expr = »(fintype.card ι, «expr + »(n, 1))) : «expr ↔ »(affine_independent k p, «expr = »(finrank k (vector_span k (set.range p)), n)) :=
begin
  have [ident hn] [":", expr nonempty ι] [],
  by simp [] [] [] ["[", "<-", expr fintype.card_pos_iff, ",", expr hc, "]"] [] [],
  cases [expr hn] ["with", ident i₁],
  rw ["[", expr affine_independent_iff_linear_independent_vsub _ _ i₁, ",", expr linear_independent_iff_card_eq_finrank_span, ",", expr eq_comm, ",", expr vector_span_range_eq_span_range_vsub_right_ne k p i₁, "]"] [],
  congr' [] [],
  rw ["<-", expr finset.card_univ] ["at", ident hc],
  rw [expr fintype.subtype_card] [],
  simp [] [] [] ["[", expr finset.filter_ne', ",", expr finset.card_erase_of_mem, ",", expr hc, "]"] [] []
end

/-- `n + 1` points are affinely independent if and only if their
`vector_span` has dimension at least `n`. -/
theorem affine_independent_iff_le_finrank_vector_span [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n+1) :
  AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.Range p)) :=
  by 
    rw [affine_independent_iff_finrank_vector_span_eq k p hc]
    split 
    ·
      rintro rfl 
      rfl
    ·
      exact fun hle => le_antisymmₓ (finrank_vector_span_range_le k p hc) hle

/-- `n + 2` points are affinely independent if and only if their
`vector_span` does not have dimension at most `n`. -/
theorem affine_independent_iff_not_finrank_vector_span_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n+2) :
  AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.Range p)) ≤ n :=
  by 
    rw [affine_independent_iff_le_finrank_vector_span k p hc, ←Nat.lt_iff_add_one_le, lt_iff_not_geₓ]

/-- `n + 2` points have a `vector_span` with dimension at most `n` if
and only if they are not affinely independent. -/
theorem finrank_vector_span_le_iff_not_affine_independent [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n+2) :
  finrank k (vectorSpan k (Set.Range p)) ≤ n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affine_independent_iff_not_finrank_vector_span_le k p hc).symm).symm

/-- A set of points is collinear if their `vector_span` has dimension
at most `1`. -/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 1

/-- The definition of `collinear`. -/
theorem collinear_iff_dim_le_one (s : Set P) : Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 :=
  Iff.rfl

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set of points, whose `vector_span` is finite-dimensional, is
collinear if and only if their `vector_span` has dimension at most
`1`. -/
theorem collinear_iff_finrank_le_one
(s : set P)
[finite_dimensional k (vector_span k s)] : «expr ↔ »(collinear k s, «expr ≤ »(finrank k (vector_span k s), 1)) :=
begin
  have [ident h] [] [":=", expr collinear_iff_dim_le_one k s],
  rw ["<-", expr finrank_eq_dim] ["at", ident h],
  exact_mod_cast [expr h]
end

variable (P)

/-- The empty set is collinear. -/
theorem collinear_empty : Collinear k (∅ : Set P) :=
  by 
    rw [collinear_iff_dim_le_one, vector_span_empty]
    simp 

variable {P}

/-- A single point is collinear. -/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) :=
  by 
    rw [collinear_iff_dim_le_one, vector_span_singleton]
    simp 

-- error in LinearAlgebra.AffineSpace.FiniteDimensional: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
theorem collinear_iff_of_mem
{s : set P}
{p₀ : P}
(h : «expr ∈ »(p₀, s)) : «expr ↔ »(collinear k s, «expr∃ , »((v : V), ∀
  p «expr ∈ » s, «expr∃ , »((r : k), «expr = »(p, «expr +ᵥ »(«expr • »(r, v), p₀))))) :=
begin
  simp_rw ["[", expr collinear_iff_dim_le_one, ",", expr dim_submodule_le_one_iff', ",", expr submodule.le_span_singleton_iff, "]"] [],
  split,
  { rintro ["⟨", ident v₀, ",", ident hv, "⟩"],
    use [expr v₀],
    intros [ident p, ident hp],
    obtain ["⟨", ident r, ",", ident hr, "⟩", ":=", expr hv «expr -ᵥ »(p, p₀) (vsub_mem_vector_span k hp h)],
    use [expr r],
    rw [expr eq_vadd_iff_vsub_eq] [],
    exact [expr hr.symm] },
  { rintro ["⟨", ident v, ",", ident hp₀v, "⟩"],
    use [expr v],
    intros [ident w, ident hw],
    have [ident hs] [":", expr «expr ≤ »(vector_span k s, «expr ∙ »(k, v))] [],
    { rw ["[", expr vector_span_eq_span_vsub_set_right k h, ",", expr submodule.span_le, ",", expr set.subset_def, "]"] [],
      intros [ident x, ident hx],
      rw ["[", expr set_like.mem_coe, ",", expr submodule.mem_span_singleton, "]"] [],
      rw [expr set.mem_image] ["at", ident hx],
      rcases [expr hx, "with", "⟨", ident p, ",", ident hp, ",", ident rfl, "⟩"],
      rcases [expr hp₀v p hp, "with", "⟨", ident r, ",", ident rfl, "⟩"],
      use [expr r],
      simp [] [] [] [] [] [] },
    have [ident hw'] [] [":=", expr set_like.le_def.1 hs hw],
    rwa [expr submodule.mem_span_singleton] ["at", ident hw'] }
end

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
  Collinear k s ↔ ∃ (p₀ : P)(v : V), ∀ p _ : p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ :=
  by 
    rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
    ·
      simp [collinear_empty]
    ·
      rw [collinear_iff_of_mem k hp₁]
      split 
      ·
        exact fun h => ⟨p₁, h⟩
      ·
        rintro ⟨p, v, hv⟩
        use v 
        intro p₂ hp₂ 
        rcases hv p₂ hp₂ with ⟨r, rfl⟩
        rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
        use r - r₁ 
        simp [vadd_vadd, ←add_smul]

/-- Two points are collinear. -/
theorem collinear_insert_singleton (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) :=
  by 
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    use p₁, p₂ -ᵥ p₁ 
    intro p hp 
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp 
    cases hp
    ·
      use 0
      simp [hp]
    ·
      use 1
      simp [hp]

/-- Three points are affinely independent if and only if they are not
collinear. -/
theorem affine_independent_iff_not_collinear (p : Finₓ 3 → P) : AffineIndependent k p ↔ ¬Collinear k (Set.Range p) :=
  by 
    rw [collinear_iff_finrank_le_one, affine_independent_iff_not_finrank_vector_span_le k p (Fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
theorem collinear_iff_not_affine_independent (p : Finₓ 3 → P) : Collinear k (Set.Range p) ↔ ¬AffineIndependent k p :=
  by 
    rw [collinear_iff_finrank_le_one, finrank_vector_span_le_iff_not_affine_independent k p (Fintype.card_fin 3)]

end AffineSpace'

