import Mathbin.Data.Fintype.Card 
import Mathbin.Data.Polynomial.RingDivision 
import Mathbin.GroupTheory.SpecificGroups.Cyclic 
import Mathbin.Algebra.GeomSum

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `is_cyclic_of_subgroup_is_domain` : A finite subgroup of the units of an integral domain
                                            is cyclic.
* `field_of_is_domain`              : A finite integral domain is a field.

## Tags

integral domain, finite integral domain, finite field
-/


section 

open Finset Polynomial Function

open_locale BigOperators Nat

section CancelMonoidWithZero

variable{M : Type _}[CancelMonoidWithZero M][Fintype M]

theorem mul_right_bijective_of_fintype₀ {a : M} (ha : a ≠ 0) : bijective fun b => a*b :=
  Fintype.injective_iff_bijective.1$ mul_right_injective₀ ha

theorem mul_left_bijective_of_fintype₀ {a : M} (ha : a ≠ 0) : bijective fun b => b*a :=
  Fintype.injective_iff_bijective.1$ mul_left_injective₀ ha

/-- Every finite nontrivial cancel_monoid_with_zero is a group_with_zero. -/
def groupWithZeroOfFintype (M : Type _) [CancelMonoidWithZero M] [DecidableEq M] [Fintype M] [Nontrivial M] :
  GroupWithZeroₓ M :=
  { ‹Nontrivial M›, ‹CancelMonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_fintype₀ h) 1,
    mul_inv_cancel :=
      fun a ha =>
        by 
          simp [HasInv.inv, dif_neg ha]
          exact Fintype.right_inverse_bij_inv _ _,
    inv_zero :=
      by 
        simp [HasInv.inv, dif_pos rfl] }

end CancelMonoidWithZero

variable{R : Type _}{G : Type _}

section Ringₓ

variable[Ringₓ R][IsDomain R][Fintype R]

/-- Every finite domain is a division ring.

TODO: Prove Wedderburn's little theorem,
which shows a finite domain is in fact commutative, hence a field. -/
def divisionRingOfIsDomain (R : Type _) [Ringₓ R] [IsDomain R] [DecidableEq R] [Fintype R] : DivisionRing R :=
  { show GroupWithZeroₓ R from groupWithZeroOfFintype R, ‹Ringₓ R› with  }

end Ringₓ

variable[CommRingₓ R][IsDomain R][Groupₓ G][Fintype G]

-- error in RingTheory.IntegralDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_nth_roots_subgroup_units
(f : «expr →* »(G, R))
(hf : injective f)
{n : exprℕ()}
(hn : «expr < »(0, n))
(g₀ : G) : «expr ≤ »(({g ∈ univ | «expr = »(«expr ^ »(g, n), g₀)} : finset G).card, (nth_roots n (f g₀)).card) :=
begin
  haveI [] [":", expr decidable_eq R] [":=", expr classical.dec_eq _],
  refine [expr le_trans _ (nth_roots n (f g₀)).to_finset_card_le],
  apply [expr card_le_card_of_inj_on f],
  { intros [ident g, ident hg],
    rw ["[", expr sep_def, ",", expr mem_filter, "]"] ["at", ident hg],
    rw ["[", expr multiset.mem_to_finset, ",", expr mem_nth_roots hn, ",", "<-", expr f.map_pow, ",", expr hg.2, "]"] [] },
  { intros [],
    apply [expr hf],
    assumption }
end

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
theorem is_cyclic_of_subgroup_is_domain (f : G →* R) (hf : injective f) : IsCyclic G :=
  by 
    classical 
    apply is_cyclic_of_card_pow_eq_one_le 
    intro n hn 
    convert le_transₓ (card_nth_roots_subgroup_units f hf hn 1) (card_nth_roots n (f 1))

/-- The unit group of a finite integral domain is cyclic.

To support `units ℤ` and other infinite monoids with finite groups of units, this requires only
`fintype (units R)` rather than deducing it from `fintype R`. -/
instance  [Fintype (Units R)] : IsCyclic (Units R) :=
  is_cyclic_of_subgroup_is_domain (Units.coeHom R)$ Units.ext

/-- Every finite integral domain is a field. -/
def fieldOfIsDomain [DecidableEq R] [Fintype R] : Field R :=
  { divisionRingOfIsDomain R, ‹CommRingₓ R› with  }

section 

variable(S : Subgroup (Units R))[Fintype S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : IsCyclic S :=
  by 
    refine' is_cyclic_of_subgroup_is_domain ⟨(coeₓ : S → R), _, _⟩ (units.ext.comp Subtype.val_injective)
    ·
      simp 
    ·
      intros 
      simp 

end 

-- error in RingTheory.IntegralDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_fiber_eq_of_mem_range
{H : Type*}
[group H]
[decidable_eq H]
(f : «expr →* »(G, H))
{x y : H}
(hx : «expr ∈ »(x, set.range f))
(hy : «expr ∈ »(y, set.range f)) : «expr = »(«expr $ »(univ.filter, λ
  g, «expr = »(f g, x)).card, «expr $ »(univ.filter, λ g, «expr = »(f g, y)).card) :=
begin
  rcases [expr hx, "with", "⟨", ident x, ",", ident rfl, "⟩"],
  rcases [expr hy, "with", "⟨", ident y, ",", ident rfl, "⟩"],
  refine [expr card_congr (λ
    g _, «expr * »(«expr * »(g, «expr ⁻¹»(x)), y)) _ _ (λ g hg, ⟨«expr * »(«expr * »(g, «expr ⁻¹»(y)), x), _⟩)],
  { simp [] [] ["only"] ["[", expr mem_filter, ",", expr one_mul, ",", expr monoid_hom.map_mul, ",", expr mem_univ, ",", expr mul_right_inv, ",", expr eq_self_iff_true, ",", expr monoid_hom.map_mul_inv, ",", expr and_self, ",", expr forall_true_iff, "]"] [] [] { contextual := tt } },
  { simp [] [] ["only"] ["[", expr mul_left_inj, ",", expr imp_self, ",", expr forall_2_true_iff, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr true_and, ",", expr mem_filter, ",", expr mem_univ, "]"] [] ["at", ident hg],
    simp [] [] ["only"] ["[", expr hg, ",", expr mem_filter, ",", expr one_mul, ",", expr monoid_hom.map_mul, ",", expr mem_univ, ",", expr mul_right_inv, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr monoid_hom.map_mul_inv, ",", expr and_self, ",", expr mul_inv_cancel_right, ",", expr inv_mul_cancel_right, "]"] [] [] }
end

-- error in RingTheory.IntegralDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
theorem sum_hom_units_eq_zero (f : «expr →* »(G, R)) (hf : «expr ≠ »(f, 1)) : «expr = »(«expr∑ , »((g : G), f g), 0) :=
begin
  classical,
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : monoid_hom.range f.to_hom_units), ∀
    y : monoid_hom.range f.to_hom_units, «expr ∈ »(y, submonoid.powers x))],
  from [expr is_cyclic.exists_monoid_generator],
  have [ident hx1] [":", expr «expr ≠ »(x, 1)] [],
  { rintro [ident rfl],
    apply [expr hf],
    ext [] [ident g] [],
    rw ["[", expr monoid_hom.one_apply, "]"] [],
    cases [expr hx ⟨f.to_hom_units g, g, rfl⟩] ["with", ident n, ident hn],
    rwa ["[", expr subtype.ext_iff, ",", expr units.ext_iff, ",", expr subtype.coe_mk, ",", expr monoid_hom.coe_to_hom_units, ",", expr one_pow, ",", expr eq_comm, "]"] ["at", ident hn] },
  replace [ident hx1] [":", expr «expr ≠ »(«expr - »((x : R), 1), 0)] [],
  from [expr λ h, hx1 (subtype.eq (units.ext (sub_eq_zero.1 h)))],
  let [ident c] [] [":=", expr (univ.filter (λ g, «expr = »(f.to_hom_units g, 1))).card],
  calc
    «expr = »(«expr∑ , »((g : G), f g), «expr∑ , »((g : G), f.to_hom_units g)) : rfl
    «expr = »(..., «expr∑ in , »((u : units R), univ.image f.to_hom_units, «expr • »((univ.filter (λ
         g, «expr = »(f.to_hom_units g, u))).card, u))) : sum_comp (coe : units R → R) f.to_hom_units
    «expr = »(..., «expr∑ in , »((u : units R), univ.image f.to_hom_units, «expr • »(c, u))) : sum_congr rfl (λ
     u hu, congr_arg2 _ _ rfl)
    «expr = »(..., «expr∑ , »((b : monoid_hom.range f.to_hom_units), «expr • »(c, «expr↑ »(b)))) : finset.sum_subtype _ (by simp [] [] [] [] [] []) _
    «expr = »(..., «expr • »(c, «expr∑ , »((b : monoid_hom.range f.to_hom_units), (b : R)))) : smul_sum.symm
    «expr = »(..., «expr • »(c, 0)) : congr_arg2 _ rfl _
    «expr = »(..., 0) : smul_zero _,
  { show [expr «expr = »((univ.filter (λ g : G, «expr = »(f.to_hom_units g, u))).card, c)],
    apply [expr card_fiber_eq_of_mem_range f.to_hom_units],
    { simpa [] [] ["only"] ["[", expr mem_image, ",", expr mem_univ, ",", expr exists_prop_of_true, ",", expr set.mem_range, "]"] [] ["using", expr hu] },
    { exact [expr ⟨1, f.to_hom_units.map_one⟩] } },
  show [expr «expr = »(«expr∑ , »((b : monoid_hom.range f.to_hom_units), (b : R)), 0)],
  calc
    «expr = »(«expr∑ , »((b : monoid_hom.range f.to_hom_units), (b : R)), «expr∑ in , »((n), range (order_of x), «expr ^ »(x, n))) : «expr $ »(eq.symm, sum_bij (λ
      n
      _, «expr ^ »(x, n)) (by simp [] [] ["only"] ["[", expr mem_univ, ",", expr forall_true_iff, "]"] [] []) (by simp [] [] ["only"] ["[", expr implies_true_iff, ",", expr eq_self_iff_true, ",", expr subgroup.coe_pow, ",", expr units.coe_pow, ",", expr coe_coe, "]"] [] []) (λ
      m
      n
      hm
      hn, pow_injective_of_lt_order_of _ (by simpa [] [] ["only"] ["[", expr mem_range, "]"] [] ["using", expr hm]) (by simpa [] [] ["only"] ["[", expr mem_range, "]"] [] ["using", expr hn])) (λ
      b hb, let ⟨n, hn⟩ := hx b in
      ⟨«expr % »(n, order_of x), mem_range.2 (nat.mod_lt _ (order_of_pos _)), by rw ["[", "<-", expr pow_eq_mod_order_of, ",", expr hn, "]"] []⟩))
    «expr = »(..., 0) : _,
  rw ["[", "<-", expr mul_left_inj' hx1, ",", expr zero_mul, ",", "<-", expr geom_sum, ",", expr geom_sum_mul, ",", expr coe_coe, "]"] [],
  norm_cast [],
  simp [] [] [] ["[", expr pow_order_of_eq_one, "]"] [] []
end

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] : (∑g : G, f g) = if f = 1 then Fintype.card G else 0 :=
  by 
    splitIfs with h h
    ·
      simp [h, card_univ]
    ·
      exact sum_hom_units_eq_zero f h

end 

