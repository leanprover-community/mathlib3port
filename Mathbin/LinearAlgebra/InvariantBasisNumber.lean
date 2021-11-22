import Mathbin.RingTheory.Ideal.Quotient 
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

It is also useful to consider two stronger conditions, namely the rank condition,
that a surjective linear map `(fin n → R) →ₗ[R] (fin m → R)` implies `m ≤ n` and
the strong rank condition, that an injective linear map `(fin n → R) →ₗ[R] (fin m → R)`
implies `n ≤ m`.

The strong rank condition implies the rank condition, and the rank condition implies
the invariant basis number property.

## Main definitions

`strong_rank_condition R` is a type class stating that `R` satisfies the strong rank condition.
`rank_condition R` is a type class stating that `R` satisfies the rank condition.
`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial left-noetherian ring satisfies the strong rank condition,
(and so in particular every division ring or field),
and then use this to show every nontrivial commutative ring has the invariant basis number property.

More generally, every commutative ring satisfies the strong rank condition. This is proved in
`linear_algebra/free_module/strong_rank_condition`. We keep
`invariant_basis_number_of_nontrivial_of_comm_ring` here since it imports fewer files.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/

## Tags

free module, rank, invariant basis number, IBN

-/


noncomputable theory

open_locale Classical BigOperators

open Function

universe u v w

section 

variable(R : Type u)[Ringₓ R]

/-- We say that `R` satisfies the strong rank condition if `(fin n → R) →ₗ[R] (fin m → R)` injective
    implies `n ≤ m`. -/
@[mkIff]
class StrongRankCondition : Prop where 
  le_of_fin_injective : ∀ {n m : ℕ} f : (Finₓ n → R) →ₗ[R] Finₓ m → R, injective f → n ≤ m

theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Finₓ n → R) →ₗ[R] Finₓ m → R) :
  injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f

-- error in LinearAlgebra.InvariantBasisNumber: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any linear map
`(fin (n + 1) → R) →ₗ[R] (fin n → R)` is not injective. -/
theorem strong_rank_condition_iff_succ : «expr ↔ »(strong_rank_condition R, ∀
 (n : exprℕ())
 (f : «expr →ₗ[ ] »(fin «expr + »(n, 1) → R, R, fin n → R)), «expr¬ »(function.injective f)) :=
begin
  refine [expr ⟨λ h n, λ f hf, _, λ h, ⟨λ n m f hf, _⟩⟩],
  { letI [] [":", expr strong_rank_condition R] [":=", expr h],
    exact [expr nat.not_succ_le_self n (le_of_fin_injective R f hf)] },
  { by_contra [ident H],
    exact [expr h m (f.comp (function.extend_by_zero.linear_map R (fin.cast_le (not_le.1 H)))) (hf.comp (function.extend_injective (rel_embedding.injective _) 0))] }
end

theorem card_le_of_injective [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β] (f : (α → R) →ₗ[R] β → R)
  (i : injective f) : Fintype.card α ≤ Fintype.card β :=
  by 
    let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
    let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
    exact
      le_of_fin_injective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
        (((LinearEquiv.symm Q).Injective.comp i).comp (LinearEquiv.injective P))

theorem card_le_of_injective' [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β] (f : (α →₀ R) →ₗ[R] β →₀ R)
  (i : injective f) : Fintype.card α ≤ Fintype.card β :=
  by 
    let P := Finsupp.linearEquivFunOnFintype R R β 
    let Q := (Finsupp.linearEquivFunOnFintype R R α).symm 
    exact card_le_of_injective R ((P.to_linear_map.comp f).comp Q.to_linear_map) ((P.injective.comp i).comp Q.injective)

/-- We say that `R` satisfies the rank condition if `(fin n → R) →ₗ[R] (fin m → R)` surjective
    implies `m ≤ n`. -/
class RankCondition : Prop where 
  le_of_fin_surjective : ∀ {n m : ℕ} f : (Finₓ n → R) →ₗ[R] Finₓ m → R, surjective f → m ≤ n

theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Finₓ n → R) →ₗ[R] Finₓ m → R) : surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f

theorem card_le_of_surjective [RankCondition R] {α β : Type _} [Fintype α] [Fintype β] (f : (α → R) →ₗ[R] β → R)
  (i : surjective f) : Fintype.card β ≤ Fintype.card α :=
  by 
    let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
    let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
    exact
      le_of_fin_surjective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
        (((LinearEquiv.symm Q).Surjective.comp i).comp (LinearEquiv.surjective P))

theorem card_le_of_surjective' [RankCondition R] {α β : Type _} [Fintype α] [Fintype β] (f : (α →₀ R) →ₗ[R] β →₀ R)
  (i : surjective f) : Fintype.card β ≤ Fintype.card α :=
  by 
    let P := Finsupp.linearEquivFunOnFintype R R β 
    let Q := (Finsupp.linearEquivFunOnFintype R R α).symm 
    exact
      card_le_of_surjective R ((P.to_linear_map.comp f).comp Q.to_linear_map) ((P.surjective.comp i).comp Q.surjective)

/--
By the universal property for free modules, any surjective map `(fin n → R) →ₗ[R] (fin m → R)`
has an injective splitting `(fin m → R) →ₗ[R] (fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
instance (priority := 100)rank_condition_of_strong_rank_condition [StrongRankCondition R] : RankCondition R :=
  { le_of_fin_surjective :=
      fun n m f s => le_of_fin_injective R _ (f.splitting_of_fun_on_fintype_surjective_injective s) }

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class InvariantBasisNumber : Prop where 
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Finₓ n → R) ≃ₗ[R] Finₓ m → R) → n = m

instance (priority := 100)invariant_basis_number_of_rank_condition [RankCondition R] : InvariantBasisNumber R :=
  { eq_of_fin_equiv :=
      fun n m e =>
        le_antisymmₓ (le_of_fin_surjective R e.symm.to_linear_map e.symm.surjective)
          (le_of_fin_surjective R e.to_linear_map e.surjective) }

end 

section 

variable(R : Type u)[Ringₓ R][InvariantBasisNumber R]

theorem eq_of_fin_equiv {n m : ℕ} : ((Finₓ n → R) ≃ₗ[R] Finₓ m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv

theorem card_eq_of_lequiv {α β : Type _} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
  Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    ((LinearEquiv.funCongrLeft R R (Fintype.equivFin α)).trans f ≪≫ₗ
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin β)).symm)

-- error in LinearAlgebra.InvariantBasisNumber: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem nontrivial_of_invariant_basis_number : nontrivial R :=
begin
  by_contra [ident h],
  refine [expr zero_ne_one (eq_of_fin_equiv R _)],
  haveI [] [] [":=", expr not_nontrivial_iff_subsingleton.1 h],
  haveI [] [":", expr subsingleton (fin 1 → R)] [":=", expr ⟨λ a b, «expr $ »(funext, λ x, subsingleton.elim _ _)⟩],
  refine [expr { .. }]; { intros [],
    exact [expr 0] } <|> tidy []
end

end 

section 

variable(R : Type u)[Ringₓ R][Nontrivial R][IsNoetherianRing R]

-- error in LinearAlgebra.InvariantBasisNumber: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/--
Any nontrivial noetherian ring satisfies the strong rank condition.

An injective map `((fin n ⊕ fin (1 + m)) → R) →ₗ[R] (fin n → R)` for some left-noetherian `R`
would force `fin (1 + m) → R ≃ₗ punit` (via `is_noetherian.equiv_punit_of_prod_injective`),
which is not the case!
-/ @[priority 100] instance noetherian_ring_strong_rank_condition : strong_rank_condition R :=
begin
  fsplit,
  intros [ident m, ident n, ident f, ident i],
  by_contradiction [ident h],
  rw ["[", expr not_le, ",", "<-", expr nat.add_one_le_iff, ",", expr le_iff_exists_add, "]"] ["at", ident h],
  obtain ["⟨", ident m, ",", ident rfl, "⟩", ":=", expr h],
  let [ident e] [":", expr «expr ≃ »(fin «expr + »(«expr + »(n, 1), m), «expr ⊕ »(fin n, fin «expr + »(1, m)))] [":=", expr (fin_congr (add_assoc _ _ _)).trans fin_sum_fin_equiv.symm],
  let [ident f'] [] [":=", expr f.comp ((linear_equiv.sum_arrow_lequiv_prod_arrow _ _ R R).symm.trans (linear_equiv.fun_congr_left R R e)).to_linear_map],
  have [ident i'] [":", expr injective f'] [":=", expr i.comp (linear_equiv.injective _)],
  apply [expr @zero_ne_one (fin «expr + »(1, m) → R) _ _],
  apply [expr (is_noetherian.equiv_punit_of_prod_injective f' i').injective],
  ext [] [] []
end

end 

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/


section 

variable{R : Type u}[CommRingₓ R](I : Ideal R){ι : Type v}[Fintype ι]{ι' : Type w}

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def induced_map (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) : (I.pi ι).Quotient → (I.pi ι').Quotient :=
  fun x =>
    Quotientₓ.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
      (by 
        refine' fun a b hab => Ideal.Quotient.eq.2 fun h => _ 
        rw [←LinearMap.map_sub]
        exact Ideal.map_pi _ _ hab e h)

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
  (I.pi ι).Quotient ≃ₗ[I.quotient] (I.pi ι').Quotient :=
  by 
    refine' { toFun := induced_map I e, invFun := induced_map I e.symm, .. }
    all_goals 
      first |
        rintro ⟨a⟩ ⟨b⟩|
        rintro ⟨a⟩
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ 
      congr 
      simp 

end 

section 

attribute [local instance] Ideal.Quotient.field

/-- Nontrivial commutative rings have the invariant basis number property. -/
instance (priority := 100)invariant_basis_number_of_nontrivial_of_comm_ring {R : Type u} [CommRingₓ R] [Nontrivial R] :
  InvariantBasisNumber R :=
  ⟨fun n m e =>
      let ⟨I, hI⟩ := Ideal.exists_maximal R 
      by 
        exactI
          eq_of_fin_equiv I.quotient ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ (induced_equiv _ e ≪≫ₗ Ideal.piQuotEquiv _ _))⟩

end 

