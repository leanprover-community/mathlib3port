import Mathbin.Algebra.Lie.IdealOperations 
import Mathbin.Algebra.Lie.Abelian 
import Mathbin.Order.PreorderHom

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `lie_algebra.derived_series_of_ideal`
  * `lie_algebra.derived_series`
  * `lie_algebra.is_solvable`
  * `lie_algebra.is_solvable_add`
  * `lie_algebra.radical`
  * `lie_algebra.radical_is_solvable`
  * `lie_algebra.derived_length_of_ideal`
  * `lie_algebra.derived_length`
  * `lie_algebra.derived_abelian_of_ideal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/


universe u v w w₁ w₂

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

namespace LieAlgebra

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derived_series_of_ideal (k : ℕ) : LieIdeal R L → LieIdeal R L :=
  (fun I => ⁅I,I⁆)^[k]

@[simp]
theorem derived_series_of_ideal_zero : derived_series_of_ideal R L 0 I = I :=
  rfl

@[simp]
theorem derived_series_of_ideal_succ (k : ℕ) :
  derived_series_of_ideal R L (k+1) I = ⁅derived_series_of_ideal R L k I,derived_series_of_ideal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I,I⁆) k I

/-- The derived series of Lie ideals of a Lie algebra. -/
abbrev derived_series (k : ℕ) : LieIdeal R L :=
  derived_series_of_ideal R L k ⊤

theorem derived_series_def (k : ℕ) : derived_series R L k = derived_series_of_ideal R L k ⊤ :=
  rfl

variable {R L}

local notation "D" => derived_series_of_ideal R L

theorem derived_series_of_ideal_add (k l : ℕ) : D (k+l) I = D k (D l I) :=
  by 
    induction' k with k ih
    ·
      rw [zero_addₓ, derived_series_of_ideal_zero]
    ·
      rw [Nat.succ_add k l, derived_series_of_ideal_succ, derived_series_of_ideal_succ, ih]

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[mono #[]]
theorem derived_series_of_ideal_le
{I J : lie_ideal R L}
{k l : exprℕ()}
(h₁ : «expr ≤ »(I, J))
(h₂ : «expr ≤ »(l, k)) : «expr ≤ »(exprD() k I, exprD() l J) :=
begin
  revert [ident l],
  induction [expr k] [] ["with", ident k, ident ih] []; intros [ident l, ident h₂],
  { rw [expr nat.le_zero_iff] ["at", ident h₂],
    rw ["[", expr h₂, ",", expr derived_series_of_ideal_zero, "]"] [],
    exact [expr h₁] },
  { have [ident h] [":", expr «expr ∨ »(«expr = »(l, k.succ), «expr ≤ »(l, k))] [],
    by rwa ["[", expr le_iff_eq_or_lt, ",", expr nat.lt_succ_iff, "]"] ["at", ident h₂],
    cases [expr h] [],
    { rw ["[", expr h, ",", expr derived_series_of_ideal_succ, ",", expr derived_series_of_ideal_succ, "]"] [],
      exact [expr lie_submodule.mono_lie _ _ _ _ (ih (le_refl k)) (ih (le_refl k))] },
    { rw [expr derived_series_of_ideal_succ] [],
      exact [expr le_trans (lie_submodule.lie_le_left _ _) (ih h)] } }
end

theorem derived_series_of_ideal_succ_le (k : ℕ) : D (k+1) I ≤ D k I :=
  derived_series_of_ideal_le (le_reflₓ I) k.le_succ

theorem derived_series_of_ideal_le_self (k : ℕ) : D k I ≤ I :=
  derived_series_of_ideal_le (le_reflₓ I) (zero_le k)

theorem derived_series_of_ideal_mono {I J : LieIdeal R L} (h : I ≤ J) (k : ℕ) : D k I ≤ D k J :=
  derived_series_of_ideal_le h (le_reflₓ k)

theorem derived_series_of_ideal_antitone {k l : ℕ} (h : l ≤ k) : D k I ≤ D l I :=
  derived_series_of_ideal_le (le_reflₓ I) h

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem derived_series_of_ideal_add_le_add
(J : lie_ideal R L)
(k l : exprℕ()) : «expr ≤ »(exprD() «expr + »(k, l) «expr + »(I, J), «expr + »(exprD() k I, exprD() l J)) :=
begin
  let [ident D₁] [":", expr «expr →ₘ »(lie_ideal R L, lie_ideal R L)] [":=", expr { to_fun := λ I, «expr⁅ , ⁆»(I, I),
     monotone' := λ I J h, lie_submodule.mono_lie I J I J h h }],
  have [ident h₁] [":", expr ∀ I J : lie_ideal R L, «expr ≤ »(D₁ «expr ⊔ »(I, J), «expr ⊔ »(D₁ I, J))] [],
  { simp [] [] [] ["[", expr lie_submodule.lie_le_right, ",", expr lie_submodule.lie_le_left, ",", expr le_sup_of_le_right, "]"] [] [] },
  rw ["<-", expr D₁.iterate_sup_le_sup_iff] ["at", ident h₁],
  exact [expr h₁ k l I J]
end

theorem derived_series_of_bot_eq_bot (k : ℕ) : derived_series_of_ideal R L k ⊥ = ⊥ :=
  by 
    rw [eq_bot_iff]
    exact derived_series_of_ideal_le_self ⊥ k

theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derived_series_of_ideal R L 1 I = ⊥ :=
  by 
    rw [derived_series_of_ideal_succ, derived_series_of_ideal_zero, LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
  IsLieAbelian (derived_series_of_ideal R L k I) ↔ derived_series_of_ideal R L (k+1) I = ⊥ :=
  by 
    rw [add_commₓ, derived_series_of_ideal_add I 1 k, abelian_iff_derived_one_eq_bot]

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

theorem derived_series_eq_derived_series_of_ideal_comap (k : ℕ) :
  derived_series R I k = (derived_series_of_ideal R L k I).comap I.incl :=
  by 
    induction' k with k ih
    ·
      simp only [derived_series_def, comap_incl_self, derived_series_of_ideal_zero]
    ·
      simp only [derived_series_def, derived_series_of_ideal_succ] at ih⊢
      rw [ih]
      exact comap_bracket_incl_of_le I (derived_series_of_ideal_le_self I k) (derived_series_of_ideal_le_self I k)

theorem derived_series_eq_derived_series_of_ideal_map (k : ℕ) :
  (derived_series R I k).map I.incl = derived_series_of_ideal R L k I :=
  by 
    rw [derived_series_eq_derived_series_of_ideal_comap, map_comap_incl, inf_eq_right]
    apply derived_series_of_ideal_le_self

theorem derived_series_eq_bot_iff (k : ℕ) : derived_series R I k = ⊥ ↔ derived_series_of_ideal R L k I = ⊥ :=
  by 
    rw [←derived_series_eq_derived_series_of_ideal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]

theorem derived_series_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derived_series R I k = ⊥)
  (hJ : derived_series R J l = ⊥) : derived_series R («expr↥ » (I+J)) (k+l) = ⊥ :=
  by 
    rw [LieIdeal.derived_series_eq_bot_iff] at hI hJ⊢
    rw [←le_bot_iff]
    let D := derived_series_of_ideal R L 
    change D k I = ⊥ at hI 
    change D l J = ⊥ at hJ 
    calc D (k+l) (I+J) ≤ D k I+D l J := derived_series_of_ideal_add_le_add I J k l _ ≤ ⊥ :=
      by 
        rw [hI, hJ]
        simp 

theorem derived_series_map_le (k : ℕ) : (derived_series R L' k).map f ≤ derived_series R L k :=
  by 
    induction' k with k ih
    ·
      simp only [derived_series_def, derived_series_of_ideal_zero, le_top]
    ·
      simp only [derived_series_def, derived_series_of_ideal_succ] at ih⊢
      exact le_transₓ (map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ ih ih)

theorem derived_series_map_eq (k : ℕ) (h : Function.Surjective f) :
  (derived_series R L' k).map f = derived_series R L k :=
  by 
    induction' k with k ih
    ·
      change (⊤ : LieIdeal R L').map f = ⊤
      rw [←f.ideal_range_eq_map]
      exact f.ideal_range_eq_top_of_surjective h
    ·
      simp only [derived_series_def, map_bracket_eq f h, ih, derived_series_of_ideal_succ]

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class is_solvable : Prop where 
  solvable : ∃ k, derived_series R L k = ⊥

instance is_solvable_bot : is_solvable R («expr↥ » (⊥ : LieIdeal R L)) :=
  ⟨⟨0, @Subsingleton.elimₓ _ LieIdeal.subsingleton_of_bot _ ⊥⟩⟩

instance is_solvable_add {I J : LieIdeal R L} [hI : is_solvable R I] [hJ : is_solvable R J] :
  is_solvable R («expr↥ » (I+J)) :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    obtain ⟨k, hk⟩ := hI 
    obtain ⟨l, hl⟩ := hJ 
    exact ⟨⟨k+l, LieIdeal.derived_series_add_eq_bot hk hl⟩⟩

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

theorem injective.lie_algebra_is_solvable [h₁ : is_solvable R L] (h₂ : injective f) : is_solvable R L' :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    obtain ⟨k, hk⟩ := h₁ 
    use k 
    apply LieIdeal.bot_of_map_eq_bot h₂ 
    rw [eq_bot_iff, ←hk]
    apply LieIdeal.derived_series_map_le

theorem surjective.lie_algebra_is_solvable [h₁ : is_solvable R L'] (h₂ : surjective f) : is_solvable R L :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    obtain ⟨k, hk⟩ := h₁ 
    use k 
    rw [←LieIdeal.derived_series_map_eq k h₂, hk]
    simp only [LieIdeal.map_eq_bot_iff, bot_le]

end Function

theorem LieHom.is_solvable_range (f : L' →ₗ⁅R⁆ L) [h : LieAlgebra.IsSolvable R L'] : LieAlgebra.IsSolvable R f.range :=
  f.surjective_range_restrict.lie_algebra_is_solvable

namespace LieAlgebra

theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : is_solvable R L' ↔ is_solvable R L :=
  by 
    split  <;> intros h
    ·
      exact e.symm.injective.lie_algebra_is_solvable
    ·
      exact e.injective.lie_algebra_is_solvable

theorem le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I ≤ J) (h₂ : is_solvable R J) : is_solvable R I :=
  (LieIdeal.hom_of_le_injective h₁).lie_algebra_is_solvable

variable (R L)

instance (priority := 100) of_abelian_is_solvable [IsLieAbelian L] : is_solvable R L :=
  by 
    use 1
    rw [←abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquivSelf]
    infer_instance

/-- The (solvable) radical of Lie algebra is the `Sup` of all solvable ideals. -/
def radical :=
  Sup { I:LieIdeal R L | is_solvable R I }

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The radical of a Noetherian Lie algebra is solvable. -/
instance radical_is_solvable [is_noetherian R L] : is_solvable R (radical R L) :=
begin
  have [ident hwf] [] [":=", expr lie_submodule.well_founded_of_noetherian R L L],
  rw ["<-", expr complete_lattice.is_sup_closed_compact_iff_well_founded] ["at", ident hwf],
  refine [expr hwf {I : lie_ideal R L | is_solvable R I} _ _],
  { use [expr «expr⊥»()],
    exact [expr lie_algebra.is_solvable_bot R L] },
  { intros [ident I, ident J, ident hI, ident hJ],
    apply [expr lie_algebra.is_solvable_add R L]; [exact [expr hI], exact [expr hJ]] }
end

/-- The `→` direction of this lemma is actually true without the `is_noetherian` assumption. -/
theorem lie_ideal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) : is_solvable R I ↔ I ≤ radical R L :=
  by 
    split  <;> intro h
    ·
      exact le_Sup h
    ·
      apply le_solvable_ideal_solvable h 
      infer_instance

theorem center_le_radical : center R L ≤ radical R L :=
  have h : is_solvable R (center R L) :=
    by 
      infer_instance 
  le_Sup h

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
noncomputable def derived_length_of_ideal (I : LieIdeal R L) : ℕ :=
  Inf { k | derived_series_of_ideal R L k I = ⊥ }

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `lie_algebra.derived_length_eq_derived_length_of_ideal`. -/
noncomputable abbrev derived_length : ℕ :=
  derived_length_of_ideal R L ⊤

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem derived_series_of_derived_length_succ
(I : lie_ideal R L)
(k : exprℕ()) : «expr ↔ »(«expr = »(derived_length_of_ideal R L I, «expr + »(k, 1)), «expr ∧ »(is_lie_abelian (derived_series_of_ideal R L k I), «expr ≠ »(derived_series_of_ideal R L k I, «expr⊥»()))) :=
begin
  rw [expr abelian_iff_derived_succ_eq_bot] [],
  let [ident s] [] [":=", expr {k | «expr = »(derived_series_of_ideal R L k I, «expr⊥»())}],
  change [expr «expr ↔ »(«expr = »(Inf s, «expr + »(k, 1)), «expr ∧ »(«expr ∈ »(«expr + »(k, 1), s), «expr ∉ »(k, s)))] [] [],
  have [ident hs] [":", expr ∀ k₁ k₂ : exprℕ(), «expr ≤ »(k₁, k₂) → «expr ∈ »(k₁, s) → «expr ∈ »(k₂, s)] [],
  { intros [ident k₁, ident k₂, ident h₁₂, ident h₁],
    suffices [] [":", expr «expr ≤ »(derived_series_of_ideal R L k₂ I, «expr⊥»())],
    { exact [expr eq_bot_iff.mpr this] },
    change [expr «expr = »(derived_series_of_ideal R L k₁ I, «expr⊥»())] [] ["at", ident h₁],
    rw ["<-", expr h₁] [],
    exact [expr derived_series_of_ideal_antitone I h₁₂] },
  exact [expr nat.Inf_upward_closed_eq_succ_iff hs k]
end

theorem derived_length_eq_derived_length_of_ideal (I : LieIdeal R L) :
  derived_length R I = derived_length_of_ideal R L I :=
  by 
    let s₁ := { k | derived_series R I k = ⊥ }
    let s₂ := { k | derived_series_of_ideal R L k I = ⊥ }
    change Inf s₁ = Inf s₂ 
    congr 
    ext k 
    exact I.derived_series_eq_bot_iff k

variable {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
noncomputable def derived_abelian_of_ideal (I : LieIdeal R L) : LieIdeal R L :=
  match derived_length_of_ideal R L I with 
  | 0 => ⊥
  | k+1 => derived_series_of_ideal R L k I

theorem abelian_derived_abelian_of_ideal (I : LieIdeal R L) : IsLieAbelian (derived_abelian_of_ideal I) :=
  by 
    dunfold derived_abelian_of_ideal 
    cases' h : derived_length_of_ideal R L I with k
    ·
      exact is_lie_abelian_bot R L
    ·
      rw [derived_series_of_derived_length_succ] at h 
      exact h.1

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem derived_length_zero
(I : lie_ideal R L)
[hI : is_solvable R I] : «expr ↔ »(«expr = »(derived_length_of_ideal R L I, 0), «expr = »(I, «expr⊥»())) :=
begin
  let [ident s] [] [":=", expr {k | «expr = »(derived_series_of_ideal R L k I, «expr⊥»())}],
  change [expr «expr ↔ »(«expr = »(Inf s, 0), _)] [] [],
  have [ident hne] [":", expr «expr ≠ »(s, «expr∅»())] [],
  { rw [expr set.ne_empty_iff_nonempty] [],
    tactic.unfreeze_local_instances,
    obtain ["⟨", ident k, ",", ident hk, "⟩", ":=", expr hI],
    use [expr k],
    rw ["[", expr derived_series_def, ",", expr lie_ideal.derived_series_eq_bot_iff, "]"] ["at", ident hk],
    exact [expr hk] },
  simp [] [] [] ["[", expr hne, "]"] [] []
end

-- error in Algebra.Lie.Solvable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem abelian_of_solvable_ideal_eq_bot_iff
(I : lie_ideal R L)
[h : is_solvable R I] : «expr ↔ »(«expr = »(derived_abelian_of_ideal I, «expr⊥»()), «expr = »(I, «expr⊥»())) :=
begin
  dunfold [ident derived_abelian_of_ideal] [],
  cases [expr h, ":", expr derived_length_of_ideal R L I] ["with", ident k],
  { rw [expr derived_length_zero] ["at", ident h],
    rw [expr h] [],
    refl },
  { obtain ["⟨", ident h₁, ",", ident h₂, "⟩", ":=", expr (derived_series_of_derived_length_succ R L I k).mp h],
    have [ident h₃] [":", expr «expr ≠ »(I, «expr⊥»())] [],
    { intros [ident contra],
      apply [expr h₂],
      rw [expr contra] [],
      apply [expr derived_series_of_bot_eq_bot] },
    change [expr «expr ↔ »(«expr = »(derived_series_of_ideal R L k I, «expr⊥»()), «expr = »(I, «expr⊥»()))] [] [],
    split; contradiction }
end

end LieAlgebra

