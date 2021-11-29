import Mathbin.Data.Equiv.Ring 
import Mathbin.GroupTheory.MonoidLocalization 
import Mathbin.RingTheory.Algebraic 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.RingTheory.Ideal.Quotient 
import Mathbin.RingTheory.IntegralClosure 
import Mathbin.RingTheory.NonZeroDivisors 
import Mathbin.Tactic.RingExp

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variables (R S P Q : Type*) [comm_ring R] [comm_ring S] [comm_ring P] [comm_ring Q]
variables [algebra R S] [algebra P Q] (M : submonoid R) (T : submonoid P)
```

## Main definitions

 * `is_localization (M : submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
   localization of `R` at `M`, i.e. the canonical map `algebra_map R S : R →+* S` is a
   localization map (satisfying the above properties).
 * `is_localization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
 * `is_localization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
   which maps elements of `M` to invertible elements of the codomain.
 * `is_localization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
   of `M` to elements of `T`
 * `is_localization.ring_equiv_of_ring_equiv`: if `R` and `P` are isomorphic by an isomorphism
   sending `M` to `T`, then `S` and `Q` are isomorphic
 * `is_localization.alg_equiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras
 * `is_localization.is_integer` is a predicate stating that `x : S` is in the image of `R`
 * `is_localization.away (x : R) S` expresses that `S` is a localization away from `x`, as an
   abbreviation of `is_localization (submonoid.powers x) S`
 * `is_localization.at_prime (I : ideal R) [is_prime I] (S : Type*)` expresses that `S` is a
   localization at (the complement of) a prime ideal `I`, as an abbreviation of
   `is_localization I.prime_compl S`
 * `is_fraction_ring R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
   `is_localization (non_zero_divisors R) K`

## Main results

 * `localization M S`, a construction of the localization as a quotient type, defined in
   `group_theory.monoid_localization`, has `comm_ring`, `algebra R` and `is_localization M`
   instances if `R` is a ring. `localization.away`, `localization.at_prime` and `fraction_ring`
   are abbreviations for `localization`s and have their corresponding `is_localization` instances
 * `is_localization.at_prime.local_ring`: a theorem (not an instance) stating a localization at the
   complement of a prime ideal is a local ring
 * `is_fraction_ring.field`: a definition (not an instance) stating the localization of an integral
   domain `R` at `R \ {0}` is a field
 * `rat.is_fraction_ring_int` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : localization_map M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `is_localization` a predicate on the `algebra_map R S`,
we can ensure the localization map commutes nicely with other `algebra_map`s.

To prove most lemmas about a localization map `algebra_map R S` in this file we invoke the
corresponding proof for the underlying `comm_monoid` localization map
`is_localization.to_localization_map M S`, which can be found in `group_theory.monoid_localization`
and the namespace `submonoid.localization_map`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `algebra_map : R →+* localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) (S : Type _) [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

open Function

open_locale BigOperators

/-- The typeclass `is_localization (M : submodule R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
class IsLocalization : Prop where 
  map_units{} : ∀ y : M, IsUnit (algebraMap R S y)
  surj{} : ∀ z : S, ∃ x : R × M, (z*algebraMap R S x.2) = algebraMap R S x.1 
  eq_iff_exists{} : ∀ {x y}, algebraMap R S x = algebraMap R S y ↔ ∃ c : M, (x*c) = y*c

variable {M S}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section 

variable (M S)

/-- `is_localization.to_localization_map M S` shows `S` is the monoid localization of `R` at `M`. -/
@[simps]
def to_localization_map : Submonoid.LocalizationMap M S :=
  { algebraMap R S with toFun := algebraMap R S, map_units' := IsLocalization.map_units _,
    surj' := IsLocalization.surj _, eq_iff_exists' := fun _ _ => IsLocalization.eq_iff_exists _ _ }

@[simp]
theorem to_localization_map_to_map : (to_localization_map M S).toMap = (algebraMap R S : R →* S) :=
  rfl

theorem to_localization_map_to_map_apply x : (to_localization_map M S).toMap x = algebraMap R S x :=
  rfl

end 

section 

variable (R)

/-- Given `a : S`, `S` a localization of `R`, `is_integer R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer (a : S) : Prop :=
  a ∈ (algebraMap R S).range

end 

theorem is_integer_zero : is_integer R (0 : S) :=
  Subring.zero_mem _

theorem is_integer_one : is_integer R (1 : S) :=
  Subring.one_mem _

theorem is_integer_add {a b : S} (ha : is_integer R a) (hb : is_integer R b) : is_integer R (a+b) :=
  Subring.add_mem _ ha hb

theorem is_integer_mul {a b : S} (ha : is_integer R a) (hb : is_integer R b) : is_integer R (a*b) :=
  Subring.mul_mem _ ha hb

theorem is_integer_smul {a : R} {b : S} (hb : is_integer R b) : is_integer R (a • b) :=
  by 
    rcases hb with ⟨b', hb⟩
    use a*b' 
    rw [←hb, (algebraMap R S).map_mul, Algebra.smul_def]

variable (M)

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, is_integer R (a*algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_scalar` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, is_integer R ((b : R) • a) :=
  by 
    simpRw [Algebra.smul_def, mul_commₓ _ a]
    apply exists_integer_multiple'

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
  Classical.some$ IsLocalization.surj _ z

@[simp]
theorem to_localization_map_sec : (to_localization_map M S).sec = sec M :=
  rfl

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
theorem sec_spec (z : S) : (z*algebraMap R S (IsLocalization.sec M z).2) = algebraMap R S (IsLocalization.sec M z).1 :=
  Classical.some_spec$ IsLocalization.surj _ z

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
theorem sec_spec' (z : S) : algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2*z :=
  by 
    rw [mul_commₓ, sec_spec]

open_locale BigOperators

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We can clear the denominators of a `finset`-indexed family of fractions. -/
theorem exist_integer_multiples
{ι : Type*}
(s : finset ι)
(f : ι → S) : «expr∃ , »((b : M), ∀ i «expr ∈ » s, is_localization.is_integer R «expr • »((b : R), f i)) :=
begin
  haveI [] [] [":=", expr classical.prop_decidable],
  refine [expr ⟨«expr∏ in , »((i), s, (sec M (f i)).2), λ i hi, ⟨_, _⟩⟩],
  { exact [expr «expr * »(«expr∏ in , »((j), s.erase i, (sec M (f j)).2), (sec M (f i)).1)] },
  rw ["[", expr ring_hom.map_mul, ",", expr sec_spec', ",", "<-", expr mul_assoc, ",", "<-", expr (algebra_map R S).map_mul, ",", "<-", expr algebra.smul_def, "]"] [],
  congr' [2] [],
  refine [expr trans _ ((submonoid.subtype M).map_prod _ _).symm],
  rw ["[", expr mul_comm, ",", "<-", expr finset.prod_insert (s.not_mem_erase i), ",", expr finset.insert_erase hi, "]"] [],
  refl
end

/-- We can clear the denominators of a `fintype`-indexed family of fractions. -/
theorem exist_integer_multiples_of_fintype {ι : Type _} [Fintype ι] (f : ι → S) :
  ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) :=
  by 
    obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f 
    exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset S) : ∃ b : M, ∀ a _ : a ∈ s, is_integer R ((b : R) • a) :=
  exist_integer_multiples M s id

variable {R M}

theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c*x) = algebraMap R S (c*y)) :
  algebraMap R S x = algebraMap R S y :=
  (to_localization_map M S).map_right_cancel h

theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x*c) = algebraMap R S (y*c)) :
  algebraMap R S x = algebraMap R S y :=
  (to_localization_map M S).map_left_cancel h

theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : (z*algebraMap R S y) = algebraMap R S x) (hx : x = 0) : z = 0 :=
  by 
    rw [hx, (algebraMap R S).map_zero] at h 
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

variable (S)

/-- `is_localization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
  (to_localization_map M S).mk' x y

@[simp]
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (to_localization_map M S).mk'_sec _

theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁*x₂) (y₁*y₂) = mk' S x₁ y₁*mk' S x₂ y₂ :=
  (to_localization_map M S).mk'_mul _ _ _ _

theorem mk'_one x : mk' S x (1 : M) = algebraMap R S x :=
  (to_localization_map M S).mk'_one _

@[simp]
theorem mk'_spec x (y : M) : (mk' S x y*algebraMap R S y) = algebraMap R S x :=
  (to_localization_map M S).mk'_spec _ _

@[simp]
theorem mk'_spec' x (y : M) : (algebraMap R S y*mk' S x y) = algebraMap R S x :=
  (to_localization_map M S).mk'_spec' _ _

@[simp]
theorem mk'_spec_mk x (y : R) (hy : y ∈ M) : (mk' S x ⟨y, hy⟩*algebraMap R S y) = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩

@[simp]
theorem mk'_spec'_mk x (y : R) (hy : y ∈ M) : (algebraMap R S y*mk' S x ⟨y, hy⟩) = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩

variable {S}

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} : z = mk' S x y ↔ (z*algebraMap R S y) = algebraMap R S x :=
  (to_localization_map M S).eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} : mk' S x y = z ↔ algebraMap R S x = z*algebraMap R S y :=
  (to_localization_map M S).mk'_eq_iff_eq_mul

variable (M)

theorem mk'_surjective (z : S) : ∃ (x : _)(y : M), mk' S x y = z :=
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩

variable {M}

theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
  mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁*y₂) = algebraMap R S (x₂*y₁) :=
  (to_localization_map M S).mk'_eq_iff_eq

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk'_mem_iff {x} {y : M} {I : ideal S} : «expr ↔ »(«expr ∈ »(mk' S x y, I), «expr ∈ »(algebra_map R S x, I)) :=
begin
  split; intro [ident h],
  { rw ["[", "<-", expr mk'_spec S x y, ",", expr mul_comm, "]"] [],
    exact [expr I.mul_mem_left (algebra_map R S y) h] },
  { rw ["<-", expr mk'_spec S x y] ["at", ident h],
    obtain ["⟨", ident b, ",", ident hb, "⟩", ":=", expr is_unit_iff_exists_inv.1 (map_units S y)],
    have [] [] [":=", expr I.mul_mem_left b h],
    rwa ["[", expr mul_comm, ",", expr mul_assoc, ",", expr hb, ",", expr mul_one, "]"] ["at", ident this] }
end

protected theorem Eq {a₁ b₁} {a₂ b₂ : M} : mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, ((a₁*b₂)*c) = (b₁*a₂)*c :=
  (to_localization_map M S).Eq

section Ext

variable [Algebra R P] [IsLocalization M P]

theorem eq_iff_eq {x y} : algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (to_localization_map M S).eq_iff_eq (to_localization_map M P)

theorem mk'_eq_iff_mk'_eq {x₁ x₂} {y₁ y₂ : M} : mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (to_localization_map M S).mk'_eq_iff_mk'_eq (to_localization_map M P)

theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : (b₁*a₂) = a₁*b₂) : mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (to_localization_map M S).mk'_eq_of_eq H

variable (S)

@[simp]
theorem mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
  (to_localization_map M S).mk'_self _ hx

@[simp]
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (to_localization_map M S).mk'_self' _

theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _

end Ext

theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) : ((algebraMap R S) x*mk' S y z) = mk' S (x*y) z :=
  (to_localization_map M S).mul_mk'_eq_mk'_of_mul _ _ _

theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x*mk' S 1 y :=
  ((to_localization_map M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y*x : R) y = (algebraMap R S) x :=
  (to_localization_map M S).mk'_mul_cancel_left _ _

theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x*y) y = (algebraMap R S) x :=
  (to_localization_map M S).mk'_mul_cancel_right _ _

@[simp]
theorem mk'_mul_mk'_eq_one (x y : M) : (mk' S (x : R) y*mk' S (y : R) x) = 1 :=
  by 
    rw [←mk'_mul, mul_commₓ] <;> exact mk'_self _ _

theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) : (mk' S x y*mk' S (y : R) ⟨x, h⟩) = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _

section 

variable (M)

theorem is_unit_comp (j : S →+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (to_localization_map M S).is_unit_comp j.to_monoid_hom _

end 

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
theorem eq_of_eq {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) {x y} (h : (algebraMap R S) x = (algebraMap R S) y) :
  g x = g y :=
  @Submonoid.LocalizationMap.eq_of_eq _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom hg _ _ h

theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) : mk' S ((x₁*y₂)+x₂*y₁) (y₁*y₂) = mk' S x₁ y₁+mk' S x₂ y₂ :=
  mk'_eq_iff_eq_mul.2$
    Eq.symm
      (by 
        rw [mul_commₓ (_+_), mul_addₓ, mul_mk'_eq_mk'_of_mul, ←eq_sub_iff_add_eq, mk'_eq_iff_eq_mul,
          mul_commₓ _ ((algebraMap R S) _), mul_sub, eq_sub_iff_add_eq, ←eq_sub_iff_add_eq', ←mul_assocₓ,
          ←(algebraMap R S).map_mul, mul_mk'_eq_mk'_of_mul, mk'_eq_iff_eq_mul]
        simp only [(algebraMap R S).map_add, Submonoid.coe_mul, (algebraMap R S).map_mul]
        ringExp)

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  RingHom.mk' (@Submonoid.LocalizationMap.lift _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom hg)$
    by 
      intro x y 
      rw [(to_localization_map M S).lift_spec, mul_commₓ, add_mulₓ, ←sub_eq_iff_eq_add, eq_comm,
        (to_localization_map M S).lift_spec_mul, mul_commₓ _ (_ - _), sub_mul, eq_sub_iff_add_eq', ←eq_sub_iff_add_eq,
        mul_assocₓ, (to_localization_map M S).lift_spec_mul]
      show (g _*g _*g _) = g _*(g _*g _) - g _*g _ 
      simp only [←g.map_sub, ←g.map_mul, to_localization_map_sec]
      apply eq_of_eq hg 
      rw [(algebraMap R S).map_mul, sec_spec', mul_sub, (algebraMap R S).map_sub]
      simp only [RingHom.map_mul, sec_spec']
      ring 
      assumption

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
theorem lift_mk' x y : lift hg (mk' S x y) = g x*«expr↑ » (IsUnit.liftRight (g.to_monoid_hom.mrestrict M) hg y⁻¹) :=
  (to_localization_map M S).lift_mk' _ _ _

theorem lift_mk'_spec x v (y : M) : lift hg (mk' S x y) = v ↔ g x = g y*v :=
  (to_localization_map M S).lift_mk'_spec _ _ _ _

@[simp]
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (to_localization_map M S).liftEq _ _

theorem lift_eq_iff {x y : R × M} : lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1*y.2) = g (y.1*x.2) :=
  (to_localization_map M S).lift_eq_iff _

@[simp]
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
  RingHom.ext$ MonoidHom.ext_iff.1$ (to_localization_map M S).lift_comp _

@[simp]
theorem lift_of_comp (j : S →+* P) : lift (is_unit_comp M j) = j :=
  RingHom.ext$ MonoidHom.ext_iff.1$ (to_localization_map M S).lift_of_comp j.to_monoid_hom

variable (M)

/-- See note [partially-applied ext lemmas] -/
theorem monoid_hom_ext ⦃j k : S →* P⦄ (h : j.comp (algebraMap R S : R →* S) = k.comp (algebraMap R S)) : j = k :=
  Submonoid.LocalizationMap.epic_of_localization_map (to_localization_map M S)$ MonoidHom.congr_fun h

/-- See note [partially-applied ext lemmas] -/
theorem ring_hom_ext ⦃j k : S →+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k :=
  RingHom.coe_monoid_hom_injective$ monoid_hom_ext M$ MonoidHom.ext$ RingHom.congr_fun h

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected theorem ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1) (hjm : ∀ a b, j (a*b) = j a*j b)
  (hkm : ∀ a b, k (a*b) = k a*k b) (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  MonoidHom.mk.inj (monoid_hom_ext M$ MonoidHom.ext h : (⟨j, hj1, hjm⟩ : S →* P) = ⟨k, hk1, hkm⟩)

variable {M}

theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext$
    MonoidHom.ext_iff.1$
      @Submonoid.LocalizationMap.lift_unique _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom hg j.to_monoid_hom
        hj

@[simp]
theorem lift_id x : lift (map_units S : ∀ y : M, IsUnit _) x = x :=
  (to_localization_map M S).lift_id _

theorem lift_surjective_iff : surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, (v*g x.2) = g x.1 :=
  (to_localization_map M S).lift_surjective_iff hg

theorem lift_injective_iff : injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (to_localization_map M S).lift_injective_iff hg

section Map

variable {T : Submonoid P} {Q : Type _} [CommRingₓ Q] (hy : M ≤ T.comap g)

variable [Algebra P Q] [IsLocalization T Q]

section 

variable (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebra_map P Q (g x) * (algebra_map P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  @lift R _ M _ _ _ _ _ _ ((algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

end 

theorem map_eq x : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp$ fun y => map_units _ ⟨g y, hy y.2⟩

theorem map_mk' x (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  @Submonoid.LocalizationMap.map_mk' _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom _ (fun y => hy y.2) _ _
    (to_localization_map T Q) _ _

@[simp]
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_reflₓ M) : map S (RingHom.id _) h z = z :=
  lift_id _

theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) : map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {A : Type _} [CommRingₓ A] {U : Submonoid A} {W} [CommRingₓ W] [Algebra A W] [IsLocalization U W]
  {l : P →+* A} (hl : T ≤ U.comap l) :
  (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun x hx => hl (hy hx) :=
  RingHom.ext$
    fun x =>
      @Submonoid.LocalizationMap.map_map _ _ _ _ _ P _ (to_localization_map M S) g _ _ _ _ _ _ _ _ _ _
        (to_localization_map U W) l _ x

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {A : Type _} [CommRingₓ A] {U : Submonoid A} {W} [CommRingₓ W] [Algebra A W] [IsLocalization U W]
  {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
  map W l hl (map Q g hy x) = map W (l.comp g) (fun x hx => hl (hy hx)) x :=
  by 
    rw [←map_comp_map hy hl] <;> rfl

section 

variable (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ring_equiv_of_ring_equiv (h : R ≃+* P) (H : M.map h.to_monoid_hom = T) : S ≃+* Q :=
  have H' : T.map h.symm.to_monoid_hom = M :=
    by 
      rw [←M.map_id, ←H, Submonoid.map_map]
      congr 
      ext 
      apply h.symm_apply_apply
  { map Q (h : R →+* P) _ with toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eqₓ H)),
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eqₓ H')),
    left_inv :=
      fun x =>
        by 
          rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
          intro x 
          convert congr_argₓ (algebraMap R S) (h.symm_apply_apply x).symm,
    right_inv :=
      fun x =>
        by 
          rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
          intro x 
          convert congr_argₓ (algebraMap P Q) (h.apply_symm_apply x).symm }

end 

theorem ring_equiv_of_ring_equiv_eq_map {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) :
  (ring_equiv_of_ring_equiv S Q j H : S →+* Q) = map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eqₓ H)) :=
  rfl

@[simp]
theorem ring_equiv_of_ring_equiv_eq {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) x :
  ring_equiv_of_ring_equiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) :=
  map_eq _ _

theorem ring_equiv_of_ring_equiv_mk' {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x : R) (y : M) :
  ring_equiv_of_ring_equiv S Q j H (mk' S x y) = mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ :=
  map_mk' _ _ _

theorem iso_comp {S T : CommRingₓₓ} [l : Algebra R S] [h : IsLocalization M S] (f : S ≅ T) :
  @IsLocalization _ _ M T _ (f.hom.comp l.to_ring_hom).toAlgebra :=
  { map_units :=
      let hm := h.1
      fun t => IsUnit.map f.hom.to_monoid_hom (hm t),
    surj :=
      let hs := h.2
      fun t =>
        let ⟨⟨r, s⟩, he⟩ := hs (f.inv t)
        ⟨⟨r, s⟩,
          by 
            convert congr_argₓ f.hom he 
            rw [RingHom.map_mul, ←CategoryTheory.comp_apply, CategoryTheory.Iso.inv_hom_id]
            rfl⟩,
    eq_iff_exists :=
      let he := h.3
      fun t t' =>
        by 
          rw [←he]
          split 
          apply f.CommRing_iso_to_ring_equiv.injective 
          exact congr_argₓ f.hom }

end Map

section AlgEquiv

variable {Q : Type _} [CommRingₓ Q] [Algebra R Q] [IsLocalization M Q]

section 

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps]
noncomputable def AlgEquiv : S ≃ₐ[R] Q :=
  { ring_equiv_of_ring_equiv S Q (RingEquiv.refl R) M.map_id with commutes' := ring_equiv_of_ring_equiv_eq _ }

end 

@[simp]
theorem alg_equiv_mk' (x : R) (y : M) : AlgEquiv M S Q (mk' S x y) = mk' Q x y :=
  map_mk' _ _ _

@[simp]
theorem alg_equiv_symm_mk' (x : R) (y : M) : (AlgEquiv M S Q).symm (mk' Q x y) = mk' S x y :=
  map_mk' _ _ _

end AlgEquiv

end IsLocalization

section Away

variable (x : R)

/-- Given `x : R`, the typeclass `is_localization.away x S` states that `S` is
isomorphic to the localization of `R` at the submonoid generated by `x`. -/
abbrev away (S : Type _) [CommRingₓ S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S

namespace Away

variable [IsLocalization.Away x S]

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `inv_self` is `(F x)⁻¹`. -/
noncomputable def inv_self : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩

variable {g : R →+* P}

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `comm_ring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def lift (hg : IsUnit (g x)) : S →+* P :=
  IsLocalization.lift$
    fun y : Submonoid.powers x =>
      show IsUnit (g y.1)by 
        obtain ⟨n, hn⟩ := y.2
        rw [←hn, g.map_pow]
        exact IsUnit.map (powMonoidHom n) hg

@[simp]
theorem away_map.lift_eq (hg : IsUnit (g x)) (a : R) : lift x hg ((algebraMap R S) a) = g a :=
  lift_eq _ _

@[simp]
theorem away_map.lift_comp (hg : IsUnit (g x)) : (lift x hg).comp (algebraMap R S) = g :=
  lift_comp _

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def away_to_away_right (y : R) [Algebra R P] [IsLocalization.Away (x*y) P] : S →+* P :=
  lift x$
    show IsUnit ((algebraMap R P) x) from
      is_unit_of_mul_eq_one ((algebraMap R P) x) (mk' P y ⟨x*y, Submonoid.mem_powers _⟩)$
        by 
          rw [mul_mk'_eq_mk'_of_mul, mk'_self]

end Away

end Away

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/


variable {M}

section 

/-- Addition in a ring localization is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨b * c + d * a, b * d⟩`.

Should not be confused with `add_localization.add`, which is defined as
`⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
-/
@[irreducible]
protected def add (z w : Localization M) : Localization M :=
  (Localization.liftOn₂ z w fun a b c d => mk (((b : R)*c)+d*a) (b*d))$
    fun a a' b b' c c' d d' h1 h2 =>
      mk_eq_mk_iff.2
        (by 
          rw [r_eq_r'] at h1 h2⊢
          cases' h1 with t₅ ht₅ 
          cases' h2 with t₆ ht₆ 
          use t₆*t₅ 
          calc (((((b : R)*c)+d*a)*b'*d')*t₆*t₅) = (((c*d')*t₆)*(b*b')*t₅)+((a*b')*t₅)*(d*d')*t₆ :=
            by 
              ring _ = (((b'*c')+d'*a')*b*d)*t₆*t₅ :=
            by 
              rw [ht₆, ht₅] <;> ring)

instance : Add (Localization M) :=
  ⟨Localization.add⟩

theorem add_mk a b c d : ((mk a b : Localization M)+mk c d) = mk ((b*c)+d*a) (b*d) :=
  by 
    unfold Add.add Localization.add 
    apply lift_on₂_mk

theorem add_mk_self a b c : ((mk a b : Localization M)+mk c b) = mk (a+c) b :=
  by 
    rw [add_mk, mk_eq_mk_iff, r_eq_r']
    refine' (r' M).symm ⟨1, _⟩
    simp only [Submonoid.coe_one, Submonoid.coe_mul]
    ring

/-- Negation in a ring localization is defined as `-⟨a, b⟩ = ⟨-a, b⟩`. -/
@[irreducible]
protected def neg (z : Localization M) : Localization M :=
  (Localization.liftOn z fun a b => mk (-a) b)$
    fun a b c d h =>
      mk_eq_mk_iff.2
        (by 
          rw [r_eq_r'] at h⊢
          cases' h with t ht 
          use t 
          rw [neg_mul_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm, ht]
          ringNF)

instance : Neg (Localization M) :=
  ⟨Localization.neg⟩

theorem neg_mk a b : -(mk a b : Localization M) = mk (-a) b :=
  by 
    unfold Neg.neg Localization.neg 
    apply lift_on_mk

/-- The zero element in a ring localization is defined as `⟨0, 1⟩`.

Should not be confused with `add_localization.zero` which is `⟨0, 0⟩`. -/
@[irreducible]
protected def zero : Localization M :=
  mk 0 1

instance : HasZero (Localization M) :=
  ⟨Localization.zero⟩

theorem mk_zero b : (mk 0 b : Localization M) = 0 :=
  calc mk 0 b = mk 0 1 :=
    mk_eq_mk_iff.mpr
      (r_of_eq
        (by 
          simp ))
    _ = 0 :=
    by 
      unfold HasZero.zero Localization.zero
    

/-- Scalar multiplication in a ring localization is defined as `c • ⟨a, b⟩ = ⟨c • a, c • b⟩`. -/
@[irreducible]
protected def smul {S : Type _} [HasScalar S R] [IsScalarTower S R R] (c : S) (z : Localization M) : Localization M :=
  (Localization.liftOn z fun a b => mk (c • a) b)$
    fun a a' b b' h =>
      mk_eq_mk_iff.2
        (by 
          cases' b with b hb 
          cases' b' with b' hb' 
          rw [r_eq_r'] at h⊢
          cases' h with t ht 
          use t 
          simp only [smul_mul_assoc, ht])

theorem smul_mk {S : Type _} [HasScalar S R] [IsScalarTower S R R] (c : S) a b :
  Localization.smul c (mk a b : Localization M) = mk (c • a) b :=
  by 
    unfold HasScalar.smul Localization.smul 
    apply lift_on_mk

private unsafe def tac :=
  sorry

instance : CommRingₓ (Localization M) :=
  { Localization.commMonoid M with zero := 0, one := 1, add := ·+·, mul := ·*·, npow := Localization.npow _,
    nsmul := Localization.smul,
    nsmul_zero' :=
      fun x =>
        Localization.induction_on x
          fun x =>
            by 
              simp only [smul_mk, zero_nsmul, mk_zero],
    nsmul_succ' :=
      fun n x =>
        Localization.induction_on x
          fun x =>
            by 
              simp only [smul_mk, succ_nsmul, add_mk_self],
    zsmul := Localization.smul,
    zsmul_zero' :=
      fun x =>
        Localization.induction_on x
          fun x =>
            by 
              simp only [smul_mk, zero_zsmul, mk_zero],
    zsmul_succ' :=
      fun n x =>
        Localization.induction_on x
          fun x =>
            by 
              simp [smul_mk, add_mk_self, -mk_eq_monoid_of_mk', add_commₓ (n : ℤ) 1, add_smul],
    zsmul_neg' :=
      fun n x =>
        Localization.induction_on x
          fun x =>
            by 
              rw [smul_mk, smul_mk, neg_mk, ←neg_smul]
              rfl,
    add_assoc :=
      fun m n k =>
        Localization.induction_on₃ m n k
          (by 
            runTac 
              tac),
    zero_add :=
      fun y =>
        Localization.induction_on y
          (by 
            runTac 
              tac),
    add_zero :=
      fun y =>
        Localization.induction_on y
          (by 
            runTac 
              tac),
    neg := Neg.neg, sub := fun x y => x+-y, sub_eq_add_neg := fun x y => rfl,
    add_left_neg :=
      fun y =>
        by 
          exact
            Localization.induction_on y
              (by 
                runTac 
                  tac),
    add_comm :=
      fun y z =>
        Localization.induction_on₂ z y
          (by 
            runTac 
              tac),
    left_distrib :=
      fun m n k =>
        Localization.induction_on₃ m n k
          (by 
            runTac 
              tac),
    right_distrib :=
      fun m n k =>
        Localization.induction_on₃ m n k
          (by 
            runTac 
              tac) }

instance : Algebra R (Localization M) :=
  RingHom.toAlgebra$
    { Localization.monoidOf M with toFun := (monoid_of M).toMap,
      map_zero' :=
        by 
          rw [←mk_zero (1 : M), mk_one_eq_monoid_of_mk],
      map_add' :=
        fun x y =>
          by 
            simp only [←mk_one_eq_monoid_of_mk, add_mk, Submonoid.coe_one, one_mulₓ, add_commₓ] }

instance : IsLocalization M (Localization M) :=
  { map_units := (Localization.monoidOf M).map_units, surj := (Localization.monoidOf M).surj,
    eq_iff_exists := fun _ _ => (Localization.monoidOf M).eq_iff_exists }

end 

@[simp]
theorem to_localization_map_eq_monoid_of : to_localization_map M (Localization M) = monoid_of M :=
  rfl

theorem monoid_of_eq_algebra_map x : (monoid_of M).toMap x = algebraMap R (Localization M) x :=
  rfl

theorem mk_one_eq_algebra_map x : mk x 1 = algebraMap R (Localization M) x :=
  rfl

theorem mk_eq_mk'_apply x y : mk x y = IsLocalization.mk' (Localization M) x y :=
  by 
    rw [mk_eq_monoid_of_mk'_apply, mk', to_localization_map_eq_monoid_of]

@[simp]
theorem mk_eq_mk' : (mk : R → M → Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoid_of_mk'

variable [IsLocalization M S]

section 

variable (M S)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps]
noncomputable def AlgEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _

end 

@[simp]
theorem alg_equiv_mk' (x : R) (y : M) : AlgEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  alg_equiv_mk' _ _

@[simp]
theorem alg_equiv_symm_mk' (x : R) (y : M) : (AlgEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  alg_equiv_symm_mk' _ _

theorem alg_equiv_mk x y : AlgEquiv M S (mk x y) = mk' S x y :=
  by 
    rw [mk_eq_mk', alg_equiv_mk']

theorem alg_equiv_symm_mk (x : R) (y : M) : (AlgEquiv M S).symm (mk' S x y) = mk x y :=
  by 
    rw [mk_eq_mk', alg_equiv_symm_mk']

end Localization

variable {M}

section AtPrime

variable (I : Ideal R) [hp : I.is_prime]

include hp

namespace Ideal

/-- The complement of a prime ideal `I ⊆ R` is a submonoid of `R`. -/
def prime_compl : Submonoid R :=
  { Carrier := («expr ᶜ» I : Set R),
    one_mem' :=
      by 
        convert I.ne_top_iff_one.1 hp.1 <;> rfl,
    mul_mem' := fun x y hnx hny hxy => Or.cases_on (hp.mem_or_mem hxy) hnx hny }

end Ideal

variable (S)

/-- Given a prime ideal `P`, the typeclass `is_localization.at_prime S P` states that `S` is
isomorphic to the localization of `R` at the complement of `P`. -/
protected abbrev IsLocalization.AtPrime :=
  IsLocalization I.prime_compl S

/-- Given a prime ideal `P`, `localization.at_prime S P` is a localization of
`R` at the complement of `P`, as a quotient type. -/
protected abbrev Localization.AtPrime :=
  Localization I.prime_compl

namespace IsLocalization

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem at_prime.local_ring [is_localization.at_prime S I] : local_ring S :=
local_of_nonunits_ideal (λ hze, begin
   rw ["[", "<-", expr (algebra_map R S).map_one, ",", "<-", expr (algebra_map R S).map_zero, "]"] ["at", ident hze],
   obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr (eq_iff_exists I.prime_compl S).1 hze],
   exact [expr (show «expr ∉ »((t : R), I), from t.2) (have htz : «expr = »((t : R), 0), by simpa [] [] [] [] [] ["using", expr ht.symm],
     «expr ▸ »(htz.symm, I.zero_mem))]
 end) (begin
   intros [ident x, ident y, ident hx, ident hy, ident hu],
   cases [expr is_unit_iff_exists_inv.1 hu] ["with", ident z, ident hxyz],
   have [] [":", expr ∀ {r : R} {s : I.prime_compl}, «expr ∈ »(mk' S r s, nonunits S) → «expr ∈ »(r, I)] [],
   from [expr λ
    (r : R)
    (s : I.prime_compl), not_imp_comm.1 (λ
     nr, is_unit_iff_exists_inv.2 ⟨mk' S «expr↑ »(s) (⟨r, nr⟩ : I.prime_compl), mk'_mul_mk'_eq_one' _ _ nr⟩)],
   rcases [expr mk'_surjective I.prime_compl x, "with", "⟨", ident rx, ",", ident sx, ",", ident hrx, "⟩"],
   rcases [expr mk'_surjective I.prime_compl y, "with", "⟨", ident ry, ",", ident sy, ",", ident hry, "⟩"],
   rcases [expr mk'_surjective I.prime_compl z, "with", "⟨", ident rz, ",", ident sz, ",", ident hrz, "⟩"],
   rw ["[", "<-", expr hrx, ",", "<-", expr hry, ",", "<-", expr hrz, ",", "<-", expr mk'_add, ",", "<-", expr mk'_mul, ",", "<-", expr mk'_self S I.prime_compl.one_mem, "]"] ["at", ident hxyz],
   rw ["<-", expr hrx] ["at", ident hx],
   rw ["<-", expr hry] ["at", ident hy],
   obtain ["⟨", ident t, ",", ident ht, "⟩", ":=", expr is_localization.eq.1 hxyz],
   simp [] [] ["only"] ["[", expr mul_one, ",", expr one_mul, ",", expr submonoid.coe_mul, ",", expr subtype.coe_mk, "]"] [] ["at", ident ht],
   rw ["[", "<-", expr sub_eq_zero, ",", "<-", expr sub_mul, "]"] ["at", ident ht],
   have [ident hr] [] [":=", expr (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right t.2],
   rw [expr sub_eq_add_neg] ["at", ident hr],
   have [] [] [":=", expr I.neg_mem_iff.1 ((ideal.add_mem_iff_right _ _).1 hr)],
   { exact [expr not_or (mt hp.mem_or_mem (not_or sx.2 sy.2)) sz.2 (hp.mem_or_mem this)] },
   { exact [expr I.mul_mem_right _ (I.add_mem (I.mul_mem_right _ (this hx)) (I.mul_mem_right _ (this hy)))] }
 end)

end IsLocalization

namespace Localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance at_prime.local_ring : LocalRing (Localization I.prime_compl) :=
  IsLocalization.AtPrime.local_ring (Localization I.prime_compl) I

end Localization

end AtPrime

namespace IsLocalization

variable [IsLocalization M S]

section Ideals

variable (M) (S)

include M

/-- Explicit characterization of the ideal given by `ideal.map (algebra_map R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_to_map_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
private def map_ideal (I : Ideal R) : Ideal S :=
  { Carrier := { z:S | ∃ x : I × M, (z*algebraMap R S x.2) = algebraMap R S x.1 },
    zero_mem' :=
      ⟨⟨0, 1⟩,
        by 
          simp ⟩,
    add_mem' :=
      by 
        rintro a b ⟨a', ha⟩ ⟨b', hb⟩
        use ⟨(a'.2*b'.1)+b'.2*a'.1, I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
        use a'.2*b'.2
        simp only [RingHom.map_add, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
        rw [add_mulₓ, ←mul_assocₓ a, ha, mul_commₓ (algebraMap R S a'.2) (algebraMap R S b'.2), ←mul_assocₓ b, hb]
        ring,
    smul_mem' :=
      by 
        rintro c x ⟨x', hx⟩
        obtain ⟨c', hc⟩ := IsLocalization.surj M c 
        use ⟨c'.1*x'.1, I.mul_mem_left c'.1 x'.1.2⟩
        use c'.2*x'.2
        simp only [←hx, ←hc, smul_eq_mul, Submodule.coe_mk, Submonoid.coe_mul, RingHom.map_mul]
        ring }

theorem mem_map_algebra_map_iff {I : Ideal R} {z} :
  z ∈ Ideal.map (algebraMap R S) I ↔ ∃ x : I × M, (z*algebraMap R S x.2) = algebraMap R S x.1 :=
  by 
    split 
    ·
      change _ → z ∈ map_ideal M S I 
      refine' fun h => Ideal.mem_Inf.1 h fun z hz => _ 
      obtain ⟨y, hy⟩ := hz 
      use
        ⟨⟨⟨y, hy.left⟩, 1⟩,
          by 
            simp [hy.right]⟩
    ·
      rintro ⟨⟨a, s⟩, h⟩
      rw [←Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_commₓ]
      exact h.symm ▸ Ideal.mem_map_of_mem _ a.2

theorem map_comap (J : Ideal S) : Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J :=
  le_antisymmₓ (Ideal.map_le_iff_le_comap.2 (le_reflₓ _))$
    fun x hJ =>
      by 
        obtain ⟨r, s, hx⟩ := mk'_surjective M x 
        rw [←hx] at hJ⊢
        exact
          Ideal.mul_mem_right _ _
            (Ideal.mem_map_of_mem _
              (show (algebraMap R S) r ∈ J from mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comap_map_of_is_prime_disjoint
(I : ideal R)
(hI : I.is_prime)
(hM : disjoint (M : set R) I) : «expr = »(ideal.comap (algebra_map R S) (ideal.map (algebra_map R S) I), I) :=
begin
  refine [expr le_antisymm (λ a ha, _) ideal.le_comap_map],
  rw ["[", expr ideal.mem_comap, ",", expr mem_map_algebra_map_iff M S, "]"] ["at", ident ha],
  obtain ["⟨", "⟨", ident b, ",", ident s, "⟩", ",", ident h, "⟩", ":=", expr ha],
  have [] [":", expr «expr = »(algebra_map R S «expr - »(«expr * »(a, «expr↑ »(s)), b), 0)] [":=", expr by simpa [] [] [] ["[", expr sub_eq_zero, "]"] [] ["using", expr h]],
  rw ["[", "<-", expr (algebra_map R S).map_zero, ",", expr eq_iff_exists M S, "]"] ["at", ident this],
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr this],
  have [] [":", expr «expr ∈ »(«expr * »(a, s), I)] [],
  { rw [expr zero_mul] ["at", ident hc],
    let [ident this] [":", expr «expr ∈ »(«expr * »(«expr - »(«expr * »(a, «expr↑ »(s)), «expr↑ »(b)), «expr↑ »(c)), I)] [":=", expr «expr ▸ »(hc.symm, I.zero_mem)],
    cases [expr hI.mem_or_mem this] ["with", ident h1, ident h2],
    { simpa [] [] [] [] [] ["using", expr I.add_mem h1 b.2] },
    { exfalso,
      refine [expr hM ⟨c.2, h2⟩] } },
  cases [expr hI.mem_or_mem this] ["with", ident h1, ident h2],
  { exact [expr h1] },
  { exfalso,
    refine [expr hM ⟨s.2, h2⟩] }
end

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def OrderEmbedding : Ideal S ↪o Ideal R :=
  { toFun := fun J => Ideal.comap (algebraMap R S) J, inj' := Function.LeftInverse.injective (map_comap M S),
    map_rel_iff' :=
      fun J₁ J₂ => ⟨fun hJ => (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ Ideal.map_mono hJ, Ideal.comap_mono⟩ }

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
theorem is_prime_iff_is_prime_disjoint
(J : ideal S) : «expr ↔ »(J.is_prime, «expr ∧ »((ideal.comap (algebra_map R S) J).is_prime, disjoint (M : set R) «expr↑ »(ideal.comap (algebra_map R S) J))) :=
begin
  split,
  { refine [expr λ h, ⟨⟨_, _⟩, λ m hm, h.ne_top (ideal.eq_top_of_is_unit_mem _ hm.2 (map_units S ⟨m, hm.left⟩))⟩],
    { refine [expr λ hJ, h.ne_top _],
      rw ["[", expr eq_top_iff, ",", "<-", expr (order_embedding M S).le_iff_le, "]"] [],
      exact [expr le_of_eq hJ.symm] },
    { intros [ident x, ident y, ident hxy],
      rw ["[", expr ideal.mem_comap, ",", expr ring_hom.map_mul, "]"] ["at", ident hxy],
      exact [expr h.mem_or_mem hxy] } },
  { refine [expr λ h, ⟨λ hJ, h.left.ne_top (eq_top_iff.2 _), _⟩],
    { rwa ["[", expr eq_top_iff, ",", "<-", expr (order_embedding M S).le_iff_le, "]"] ["at", ident hJ] },
    { intros [ident x, ident y, ident hxy],
      obtain ["⟨", ident a, ",", ident s, ",", ident ha, "⟩", ":=", expr mk'_surjective M x],
      obtain ["⟨", ident b, ",", ident t, ",", ident hb, "⟩", ":=", expr mk'_surjective M y],
      have [] [":", expr «expr ∈ »(mk' S «expr * »(a, b) «expr * »(s, t), J)] [":=", expr by rwa ["[", expr mk'_mul, ",", expr ha, ",", expr hb, "]"] []],
      rw ["[", expr mk'_mem_iff, ",", "<-", expr ideal.mem_comap, "]"] ["at", ident this],
      replace [ident this] [] [":=", expr h.left.mem_or_mem this],
      rw ["[", expr ideal.mem_comap, ",", expr ideal.mem_comap, "]"] ["at", ident this],
      rwa ["[", "<-", expr ha, ",", "<-", expr hb, ",", expr mk'_mem_iff, ",", expr mk'_mem_iff, "]"] [] } }
end

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem is_prime_of_is_prime_disjoint (I : Ideal R) (hp : I.is_prime) (hd : Disjoint (M : Set R) («expr↑ » I)) :
  (Ideal.map (algebraMap R S) I).IsPrime :=
  by 
    rw [is_prime_iff_is_prime_disjoint M S, comap_map_of_is_prime_disjoint M S I hp hd]
    exact ⟨hp, hd⟩

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def order_iso_of_prime :
  { p : Ideal S // p.is_prime } ≃o { p : Ideal R // p.is_prime ∧ Disjoint (M : Set R) («expr↑ » p) } :=
  { toFun := fun p => ⟨Ideal.comap (algebraMap R S) p.1, (is_prime_iff_is_prime_disjoint M S p.1).1 p.2⟩,
    invFun := fun p => ⟨Ideal.map (algebraMap R S) p.1, is_prime_of_is_prime_disjoint M S p.1 p.2.1 p.2.2⟩,
    left_inv := fun J => Subtype.eq (map_comap M S J),
    right_inv := fun I => Subtype.eq (comap_map_of_is_prime_disjoint M S I.1 I.2.1 I.2.2),
    map_rel_iff' :=
      fun I I' =>
        ⟨fun h => show I.val ≤ I'.val from map_comap M S I.val ▸ map_comap M S I'.val ▸ Ideal.map_mono h,
          fun h x hx => h hx⟩ }

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `quotient_map` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
theorem surjective_quotient_map_of_maximal_of_localization
{I : ideal S}
[I.is_prime]
{J : ideal R}
{H : «expr ≤ »(J, I.comap (algebra_map R S))}
(hI : (I.comap (algebra_map R S)).is_maximal) : function.surjective (I.quotient_map (algebra_map R S) H) :=
begin
  intro [ident s],
  obtain ["⟨", ident s, ",", ident rfl, "⟩", ":=", expr ideal.quotient.mk_surjective s],
  obtain ["⟨", ident r, ",", "⟨", ident m, ",", ident hm, "⟩", ",", ident rfl, "⟩", ":=", expr mk'_surjective M s],
  by_cases [expr hM, ":", expr «expr = »(ideal.quotient.mk (I.comap (algebra_map R S)) m, 0)],
  { have [] [":", expr «expr = »(I, «expr⊤»())] [],
    { rw [expr ideal.eq_top_iff_one] [],
      rw ["[", expr ideal.quotient.eq_zero_iff_mem, ",", expr ideal.mem_comap, "]"] ["at", ident hM],
      convert [] [expr I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM] [],
      rw ["[", "<-", expr mk'_eq_mul_mk'_one, ",", expr mk'_self, "]"] [] },
    exact [expr ⟨0, eq_comm.1 (by simp [] [] [] ["[", expr ideal.quotient.eq_zero_iff_mem, ",", expr this, "]"] [] [])⟩] },
  { rw [expr ideal.quotient.maximal_ideal_iff_is_field_quotient] ["at", ident hI],
    obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr hI.3 hM],
    obtain ["⟨", ident rn, ",", ident rfl, "⟩", ":=", expr ideal.quotient.mk_surjective n],
    refine [expr ⟨ideal.quotient.mk J «expr * »(r, rn), _⟩],
    rw ["<-", expr ring_hom.map_mul] ["at", ident hn],
    replace [ident hn] [] [":=", expr congr_arg (ideal.quotient_map I (algebra_map R S) le_rfl) hn],
    simp [] [] ["only"] ["[", expr ring_hom.map_one, ",", expr ideal.quotient_map_mk, ",", expr ring_hom.map_mul, "]"] [] ["at", ident hn],
    rw ["[", expr ideal.quotient_map_mk, ",", "<-", expr sub_eq_zero, ",", "<-", expr ring_hom.map_sub, ",", expr ideal.quotient.eq_zero_iff_mem, ",", "<-", expr ideal.quotient.eq_zero_iff_mem, ",", expr ring_hom.map_sub, ",", expr sub_eq_zero, ",", expr mk'_eq_mul_mk'_one, "]"] [],
    simp [] [] ["only"] ["[", expr mul_eq_mul_left_iff, ",", expr ring_hom.map_mul, "]"] [] [],
    exact [expr or.inl (mul_left_cancel₀ (λ
       hn, hM (ideal.quotient.eq_zero_iff_mem.2 (ideal.mem_comap.2 (ideal.quotient.eq_zero_iff_mem.1 hn)))) (trans hn (by rw ["[", "<-", expr ring_hom.map_mul, ",", "<-", expr mk'_eq_mul_mk'_one, ",", expr mk'_self, ",", expr ring_hom.map_one, "]"] [])))] }
end

end Ideals

section AtUnits

variable (R) (S) (M)

/-- The localization at a module of units is isomorphic to the ring -/
noncomputable def at_units (H : ∀ x : M, IsUnit (x : R)) : R ≃ₐ[R] S :=
  by 
    refine' AlgEquiv.ofBijective (Algebra.ofId R S) ⟨_, _⟩
    ·
      intro x y hxy 
      obtain ⟨c, eq⟩ := (IsLocalization.eq_iff_exists M S).mp hxy 
      obtain ⟨u, hu⟩ := H c 
      rwa [←hu, Units.mul_left_inj] at eq
    ·
      intro y 
      obtain ⟨⟨x, s⟩, eq⟩ := IsLocalization.surj M y 
      obtain ⟨u, hu⟩ := H s 
      use x*u.inv 
      dsimp only [Algebra.ofId, RingHom.to_fun_eq_coe, AlgHom.coe_mk]
      rw [RingHom.map_mul, ←Eq, ←hu, mul_assocₓ, ←RingHom.map_mul]
      simp 

/-- The localization away from a unit is isomorphic to the ring -/
noncomputable def at_unit (x : R) (e : IsUnit x) [IsLocalization.Away x S] : R ≃ₐ[R] S :=
  by 
    apply at_units R (Submonoid.powers x)
    rintro ⟨xn, n, hxn⟩
    obtain ⟨u, hu⟩ := e 
    rw [is_unit_iff_exists_inv]
    use u.inv^n 
    simp [←hxn, ←hu, ←mul_powₓ]

/-- The localization at one is isomorphic to the ring. -/
noncomputable def at_one [IsLocalization.Away (1 : R) S] : R ≃ₐ[R] S :=
  @at_unit R _ S _ _ (1 : R) is_unit_one _

end AtUnits

variable (S)

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
def coe_submodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I

theorem mem_coe_submodule (I : Ideal R) {x : S} : x ∈ coe_submodule S I ↔ ∃ y : R, y ∈ I ∧ algebraMap R S y = x :=
  Iff.rfl

theorem coe_submodule_mono {I J : Ideal R} (h : I ≤ J) : coe_submodule S I ≤ coe_submodule S J :=
  Submodule.map_mono h

@[simp]
theorem coe_submodule_bot : coe_submodule S (⊥ : Ideal R) = ⊥ :=
  by 
    rw [coe_submodule, Submodule.map_bot]

@[simp]
theorem coe_submodule_top : coe_submodule S (⊤ : Ideal R) = 1 :=
  by 
    rw [coe_submodule, Submodule.map_top, Submodule.one_eq_range]

@[simp]
theorem coe_submodule_sup (I J : Ideal R) : coe_submodule S (I⊔J) = coe_submodule S I⊔coe_submodule S J :=
  Submodule.map_sup _ _ _

@[simp]
theorem coe_submodule_mul (I J : Ideal R) : coe_submodule S (I*J) = coe_submodule S I*coe_submodule S J :=
  Submodule.map_mul _ _ (Algebra.ofId R S)

theorem coe_submodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
  Submodule.Fg (coe_submodule S I) ↔ Submodule.Fg I :=
  ⟨Submodule.fg_of_fg_map _ (LinearMap.ker_eq_bot.mpr hS), Submodule.fg_map⟩

@[simp]
theorem coe_submodule_span (s : Set R) : coe_submodule S (Ideal.span s) = Submodule.span R (algebraMap R S '' s) :=
  by 
    rw [IsLocalization.coeSubmodule, Ideal.span, Submodule.map_span]
    rfl

@[simp]
theorem coe_submodule_span_singleton (x : R) :
  coe_submodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x} :=
  by 
    rw [coe_submodule_span, Set.image_singleton]

variable {g : R →+* P}

variable {T : Submonoid P} (hy : M ≤ T.comap g) {Q : Type _} [CommRingₓ Q]

variable [Algebra P Q] [IsLocalization T Q]

theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x :=
  by 
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, map_eq]

section 

include M

theorem IsNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S :=
  by 
    rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at h⊢
    exact OrderEmbedding.well_founded (IsLocalization.orderEmbedding M S).dual h

end 

section IntegerNormalization

open Polynomial

open_locale Classical

variable (M) {S}

/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeff_integer_normalization (p : Polynomial S) (i : ℕ) : R :=
  if hi : i ∈ p.support then
    Classical.some
      (Classical.some_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff)) (p.coeff i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  else 0

theorem coeff_integer_normalization_of_not_mem_support (p : Polynomial S) (i : ℕ) (h : coeff p i = 0) :
  coeff_integer_normalization M p i = 0 :=
  by 
    simp only [coeff_integer_normalization, h, mem_support_iff, eq_self_iff_true, not_true, Ne.def, dif_neg,
      not_false_iff]

theorem coeff_integer_normalization_mem_support (p : Polynomial S) (i : ℕ) (h : coeff_integer_normalization M p i ≠ 0) :
  i ∈ p.support :=
  by 
    contrapose h 
    rw [Ne.def, not_not, coeff_integer_normalization, dif_neg h]

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integer_normalization (p : Polynomial S) : Polynomial R :=
  ∑i in p.support, monomial i (coeff_integer_normalization M p i)

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem integer_normalization_coeff
(p : polynomial S)
(i : exprℕ()) : «expr = »((integer_normalization M p).coeff i, coeff_integer_normalization M p i) :=
by simp [] [] [] ["[", expr integer_normalization, ",", expr coeff_monomial, ",", expr coeff_integer_normalization_of_not_mem_support, "]"] [] [] { contextual := tt }

theorem integer_normalization_spec (p : Polynomial S) :
  ∃ b : M, ∀ i, algebraMap R S ((integer_normalization M p).coeff i) = (b : R) • p.coeff i :=
  by 
    use Classical.some (exist_integer_multiples_of_finset M (p.support.image p.coeff))
    intro i 
    rw [integer_normalization_coeff, coeff_integer_normalization]
    splitIfs with hi
    ·
      exact
        Classical.some_spec
          (Classical.some_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff)) (p.coeff i)
            (finset.mem_image.mpr ⟨i, hi, rfl⟩))
    ·
      convert (smul_zero _).symm
      ·
        apply RingHom.map_zero
      ·
        exact not_mem_support_iff.mp hi

theorem integer_normalization_map_to_map (p : Polynomial S) :
  ∃ b : M, (integer_normalization M p).map (algebraMap R S) = (b : R) • p :=
  let ⟨b, hb⟩ := integer_normalization_spec M p
  ⟨b,
    Polynomial.ext
      fun i =>
        by 
          rw [coeff_map, coeff_smul]
          exact hb i⟩

variable {R' : Type _} [CommRingₓ R']

theorem integer_normalization_eval₂_eq_zero (g : S →+* R') (p : Polynomial S) {x : R'} (hx : eval₂ g x p = 0) :
  eval₂ (g.comp (algebraMap R S)) x (integer_normalization M p) = 0 :=
  let ⟨b, hb⟩ := integer_normalization_map_to_map M p 
  trans (eval₂_map (algebraMap R S) g x).symm
    (by 
      rw [hb, ←IsScalarTower.algebra_map_smul S (b : R) p, eval₂_smul, hx, mul_zero])

theorem integer_normalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R'] (p : Polynomial S)
  {x : R'} (hx : aeval x p = 0) : aeval x (integer_normalization M p) = 0 :=
  by 
    rw [aeval_def, IsScalarTower.algebra_map_eq R S R', integer_normalization_eval₂_eq_zero _ _ _ hx]

end IntegerNormalization

variable {R M} (S) {K : Type _}

theorem to_map_eq_zero_iff {x : R} (hM : M ≤ nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 :=
  by 
    rw [←(algebraMap R S).map_zero]
    split  <;> intro h
    ·
      cases' (eq_iff_exists M S).mp h with c hc 
      rw [zero_mul] at hc 
      exact hM c.2 x hc
    ·
      rw [h]

protected theorem injective (hM : M ≤ nonZeroDivisors R) : injective (algebraMap R S) :=
  by 
    rw [RingHom.injective_iff (algebraMap R S)]
    intro a ha 
    rwa [to_map_eq_zero_iff S hM] at ha

protected theorem to_map_ne_zero_of_mem_non_zero_divisors [Nontrivial R] (hM : M ≤ nonZeroDivisors R) {x : R}
  (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ≠ 0 :=
  show (algebraMap R S).toMonoidWithZeroHom x ≠ 0 from
    (algebraMap R S).map_ne_zero_of_mem_non_zero_divisors (IsLocalization.injective S hM) hx

variable (S Q M)

/-- Injectivity of a map descends to the map induced on localizations. -/
theorem map_injective_of_injective (hg : Function.Injective g) [IsLocalization (M.map g : Submonoid P) Q]
  (hM : (M.map g : Submonoid P) ≤ nonZeroDivisors P) : Function.Injective (map Q g M.le_comap_map : S → Q) :=
  by 
    rintro x y hxy 
    obtain ⟨a, b, rfl⟩ := mk'_surjective M x 
    obtain ⟨c, d, rfl⟩ := mk'_surjective M y 
    rw [map_mk' _ a b, map_mk' _ c d, mk'_eq_iff_eq] at hxy 
    refine' mk'_eq_iff_eq.2 (congr_argₓ (algebraMap _ _) (hg _))
    convert IsLocalization.injective _ hM hxy <;> simp 

variable {S Q M}

@[mono]
theorem coe_submodule_le_coe_submodule (h : M ≤ nonZeroDivisors R) {I J : Ideal R} :
  coe_submodule S I ≤ coe_submodule S J ↔ I ≤ J :=
  Submodule.map_le_map_iff_of_injective (IsLocalization.injective _ h) _ _

@[mono]
theorem coe_submodule_strict_mono (h : M ≤ nonZeroDivisors R) :
  StrictMono (coe_submodule S : Ideal R → Submodule R S) :=
  strict_mono_of_le_iff_le fun _ _ => (coe_submodule_le_coe_submodule h).symm

variable (S) {Q M}

theorem coe_submodule_injective (h : M ≤ nonZeroDivisors R) :
  Function.Injective (coe_submodule S : Ideal R → Submodule R S) :=
  injective_of_le_imp_le _ fun _ _ => (coe_submodule_le_coe_submodule h).mp

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coe_submodule_is_principal
{I : ideal R}
(h : «expr ≤ »(M, non_zero_divisors R)) : «expr ↔ »((coe_submodule S I).is_principal, I.is_principal) :=
begin
  split; unfreezingI { rintros ["⟨", "⟨", ident x, ",", ident hx, "⟩", "⟩"] },
  { have [ident x_mem] [":", expr «expr ∈ »(x, coe_submodule S I)] [":=", expr «expr ▸ »(hx.symm, submodule.mem_span_singleton_self x)],
    obtain ["⟨", ident x, ",", ident x_mem, ",", ident rfl, "⟩", ":=", expr (mem_coe_submodule _ _).mp x_mem],
    refine [expr ⟨⟨x, coe_submodule_injective S h _⟩⟩],
    rw ["[", expr ideal.submodule_span_eq, ",", expr hx, ",", expr coe_submodule_span_singleton, "]"] [] },
  { refine [expr ⟨⟨algebra_map R S x, _⟩⟩],
    rw ["[", expr hx, ",", expr ideal.submodule_span_eq, ",", expr coe_submodule_span_singleton, "]"] [] }
end

variable {A : Type _} [CommRingₓ A] [IsDomain A]

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A `comm_ring` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_of_le_non_zero_divisors
[algebra A S]
{M : submonoid A}
[is_localization M S]
(hM : «expr ≤ »(M, non_zero_divisors A)) : is_domain S :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := begin
    intros [ident z, ident w, ident h],
    cases [expr surj M z] ["with", ident x, ident hx],
    cases [expr surj M w] ["with", ident y, ident hy],
    have [] [":", expr «expr = »(«expr * »(«expr * »(«expr * »(z, w), algebra_map A S y.2), algebra_map A S x.2), «expr * »(algebra_map A S x.1, algebra_map A S y.1))] [],
    by rw ["[", expr mul_assoc z, ",", expr hy, ",", "<-", expr hx, "]"] []; ac_refl,
    rw ["[", expr h, ",", expr zero_mul, ",", expr zero_mul, ",", "<-", expr (algebra_map A S).map_mul, "]"] ["at", ident this],
    cases [expr eq_zero_or_eq_zero_of_mul_eq_zero ((to_map_eq_zero_iff S hM).mp this.symm)] ["with", ident H, ident H],
    { exact [expr or.inl (eq_zero_of_fst_eq_zero hx H)] },
    { exact [expr or.inr (eq_zero_of_fst_eq_zero hy H)] }
  end,
  exists_pair_ne := ⟨algebra_map A S 0, algebra_map A S 1, λ h, zero_ne_one (is_localization.injective S hM h)⟩ }

/-- The localization at of an integral domain to a set of non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_localization {M : Submonoid A} (hM : M ≤ nonZeroDivisors A) : IsDomain (Localization M) :=
  is_domain_of_le_non_zero_divisors _ hM

/--
The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
instance is_domain_of_local_at_prime {P : Ideal A} (hp : P.is_prime) : IsDomain (Localization.AtPrime P) :=
  is_domain_localization (le_non_zero_divisors_of_no_zero_divisors (not_not_intro P.zero_mem))

namespace AtPrime

variable (I : Ideal R) [hI : I.is_prime] [IsLocalization.AtPrime S I]

include hI

theorem is_unit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x ∈ I.prime_compl :=
  ⟨fun h hx =>
      (is_prime_of_is_prime_disjoint I.prime_compl S I hI disjoint_compl_left).ne_top$
        (Ideal.map (algebraMap R S) I).eq_top_of_is_unit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

theorem to_map_mem_maximal_iff (x : R) (h : _root_.local_ring S := LocalRing S I) :
  algebraMap R S x ∈ LocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp$
    by 
      simpa only [@LocalRing.mem_maximal_ideal S, mem_nonunits_iff, not_not] using is_unit_to_map_iff S I x

theorem is_unit_mk'_iff (x : R) (y : I.prime_compl) : IsUnit (mk' S x y) ↔ x ∈ I.prime_compl :=
  ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h,
    fun h => is_unit_iff_exists_inv.mpr ⟨mk' S («expr↑ » y) ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

theorem mk'_mem_maximal_iff (x : R) (y : I.prime_compl) (h : _root_.local_ring S := LocalRing S I) :
  mk' S x y ∈ LocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp$
    by 
      simpa only [@LocalRing.mem_maximal_ideal S, mem_nonunits_iff, not_not] using is_unit_mk'_iff S I x y

end AtPrime

end IsLocalization

namespace Localization

open IsLocalization

attribute [local instance] Classical.propDecidable

variable (I : Ideal R) [hI : I.is_prime]

include hI

variable {I}

/-- The unique maximal ideal of the localization at `I.prime_compl` lies over the ideal `I`. -/
theorem at_prime.comap_maximal_ideal :
  Ideal.comap (algebraMap R (Localization.AtPrime I)) (LocalRing.maximalIdeal (Localization I.prime_compl)) = I :=
  Ideal.ext$
    fun x =>
      by 
        simpa only [Ideal.mem_comap] using at_prime.to_map_mem_maximal_iff _ I x

/-- The image of `I` in the localization at `I.prime_compl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `at_prime.local_ring` -/
theorem at_prime.map_eq_maximal_ideal :
  Ideal.map (algebraMap R (Localization.AtPrime I)) I = LocalRing.maximalIdeal (Localization I.prime_compl) :=
  by 
    convert congr_argₓ (Ideal.map _) at_prime.comap_maximal_ideal.symm 
    rw [map_comap I.prime_compl]

theorem le_comap_prime_compl_iff {J : Ideal P} [hJ : J.is_prime] {f : R →+* P} :
  I.prime_compl ≤ J.prime_compl.comap f ↔ J.comap f ≤ I :=
  ⟨fun h x hx =>
      by 
        contrapose! hx 
        exact h hx,
    fun h x hx hfxJ => hx (h hfxJ)⟩

variable (I)

/--
For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, together with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to `J.comap f`.
 -/
noncomputable def local_ring_hom (J : Ideal P) [hJ : J.is_prime] (f : R →+* P) (hIJ : I = J.comap f) :
  Localization.AtPrime I →+* Localization.AtPrime J :=
  IsLocalization.map (Localization.AtPrime J) f (le_comap_prime_compl_iff.mpr (ge_of_eq hIJ))

theorem local_ring_hom_to_map (J : Ideal P) [hJ : J.is_prime] (f : R →+* P) (hIJ : I = J.comap f) (x : R) :
  local_ring_hom I J f hIJ (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  map_eq _ _

theorem local_ring_hom_mk' (J : Ideal P) [hJ : J.is_prime] (f : R →+* P) (hIJ : I = J.comap f) (x : R)
  (y : I.prime_compl) :
  local_ring_hom I J f hIJ (IsLocalization.mk' _ x y) =
    IsLocalization.mk' (Localization.AtPrime J) (f x)
      (⟨f y, le_comap_prime_compl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.prime_compl) :=
  map_mk' _ _ _

instance is_local_ring_hom_local_ring_hom (J : Ideal P) [hJ : J.is_prime] (f : R →+* P) (hIJ : I = J.comap f) :
  IsLocalRingHom (local_ring_hom I J f hIJ) :=
  IsLocalRingHom.mk$
    fun x hx =>
      by 
        rcases IsLocalization.mk'_surjective I.prime_compl x with ⟨r, s, rfl⟩
        rw [local_ring_hom_mk'] at hx 
        rw [at_prime.is_unit_mk'_iff] at hx⊢
        exact fun hr => hx ((set_like.ext_iff.mp hIJ r).mp hr)

theorem local_ring_hom_unique (J : Ideal P) [hJ : J.is_prime] (f : R →+* P) (hIJ : I = J.comap f)
  {j : Localization.AtPrime I →+* Localization.AtPrime J} (hj : ∀ x : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) :
  local_ring_hom I J f hIJ = j :=
  map_unique _ _ hj

@[simp]
theorem local_ring_hom_id : local_ring_hom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _ :=
  local_ring_hom_unique _ _ _ _ fun x => rfl

@[simp]
theorem local_ring_hom_comp {S : Type _} [CommRingₓ S] (J : Ideal S) [hJ : J.is_prime] (K : Ideal P) [hK : K.is_prime]
  (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
  local_ring_hom I K (g.comp f)
      (by 
        rw [hIJ, hJK, Ideal.comap_comap f g]) =
    (local_ring_hom J K g hJK).comp (local_ring_hom I J f hIJ) :=
  local_ring_hom_unique _ _ _ _
    fun r =>
      by 
        simp only [Function.comp_app, RingHom.coe_comp, local_ring_hom_to_map]

end Localization

open IsLocalization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem localization_map_bijective_of_field {R Rₘ : Type _} [CommRingₓ R] [IsDomain R] [CommRingₓ Rₘ] {M : Submonoid R}
  (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] : Function.Bijective (algebraMap R Rₘ) :=
  by 
    refine' ⟨IsLocalization.injective _ (le_non_zero_divisors_of_no_zero_divisors hM), fun x => _⟩
    obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x 
    obtain ⟨n, hn⟩ := hR.mul_inv_cancel (fun hm0 => hM (hm0 ▸ hm) : m ≠ 0)
    exact
      ⟨r*n,
        by 
          erw [eq_mk'_iff_mul_eq, ←RingHom.map_mul, mul_assocₓ, mul_commₓ n, hn, mul_oneₓ]⟩

variable (R) {A : Type _} [CommRingₓ A] [IsDomain A]

variable (K : Type _)

/-- `is_fraction_ring R K` states `K` is the field of fractions of an integral domain `R`. -/
abbrev IsFractionRing [CommRingₓ K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K

/-- The cast from `int` to `rat` as a `fraction_ring`. -/
instance Rat.is_fraction_ring : IsFractionRing ℤ ℚ :=
  { map_units :=
      by 
        rintro ⟨x, hx⟩
        rw [mem_non_zero_divisors_iff_ne_zero] at hx 
        simpa only [RingHom.eq_int_cast, is_unit_iff_ne_zero, Int.cast_eq_zero, Ne.def, Subtype.coe_mk] using hx,
    surj :=
      by 
        rintro ⟨n, d, hd, h⟩
        refine' ⟨⟨n, ⟨d, _⟩⟩, Rat.mul_denom_eq_num⟩
        rwa [mem_non_zero_divisors_iff_ne_zero, Int.coe_nat_ne_zero_iff_pos],
    eq_iff_exists :=
      by 
        intro x y 
        rw [RingHom.eq_int_cast, RingHom.eq_int_cast, Int.cast_inj]
        refine'
          ⟨by 
              rintro rfl 
              use 1,
            _⟩
        rintro ⟨⟨c, hc⟩, h⟩
        apply Int.eq_of_mul_eq_mul_right _ h 
        rwa [mem_non_zero_divisors_iff_ne_zero] at hc }

namespace IsFractionRing

variable {R K}

section CommRingₓ

variable [CommRingₓ K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  to_map_eq_zero_iff _ (le_of_eqₓ rfl)

variable (R K)

protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eqₓ rfl)

variable {R K}

@[simp, mono]
theorem coe_submodule_le_coe_submodule {I J : Ideal R} : coe_submodule K I ≤ coe_submodule K J ↔ I ≤ J :=
  IsLocalization.coe_submodule_le_coe_submodule (le_reflₓ _)

@[mono]
theorem coe_submodule_strict_mono : StrictMono (coe_submodule K : Ideal R → Submodule R K) :=
  strict_mono_of_le_iff_le fun _ _ => coe_submodule_le_coe_submodule.symm

variable (R K)

theorem coe_submodule_injective : Function.Injective (coe_submodule K : Ideal R → Submodule R K) :=
  injective_of_le_imp_le _ fun _ _ => coe_submodule_le_coe_submodule.mp

@[simp]
theorem coe_submodule_is_principal {I : Ideal R} : (coe_submodule K I).IsPrincipal ↔ I.is_principal :=
  IsLocalization.coe_submodule_is_principal _ (le_reflₓ _)

variable {R K}

protected theorem to_map_ne_zero_of_mem_non_zero_divisors [Nontrivial R] {x : R} (hx : x ∈ nonZeroDivisors R) :
  algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_non_zero_divisors _ (le_reflₓ _) hx

variable (A)

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem IsDomain : IsDomain K :=
  is_domain_of_le_non_zero_divisors K (le_reflₓ (nonZeroDivisors A))

attribute [local instance] Classical.decEq

/-- The inverse of an element in the field of fractions of an integral domain. -/
@[irreducible]
protected noncomputable def inv (z : K) : K :=
  if h : z = 0 then 0 else
    mk' K («expr↑ » (sec (nonZeroDivisors A) z).2)
      ⟨(sec _ z).1,
        mem_non_zero_divisors_iff_ne_zero.2$ fun h0 => h$ eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩

attribute [local semireducible] IsFractionRing.inv

protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : (x*IsFractionRing.inv A x) = 1 :=
  show (x*dite _ _ _) = 1by 
    rw [dif_neg hx,
        ←IsUnit.mul_left_inj
          (map_units K
            ⟨(sec _ x).1,
              mem_non_zero_divisors_iff_ne_zero.2$
                fun h0 => hx$ eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
        one_mulₓ, mul_assocₓ, mk'_spec, ←eq_mk'_iff_mul_eq] <;>
      exact (mk'_sec _ x).symm

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def to_field : Field K :=
  { IsFractionRing.is_domain A,
    show CommRingₓ K by 
      infer_instance with
    inv := IsFractionRing.inv A, mul_inv_cancel := IsFractionRing.mul_inv_cancel A, inv_zero := dif_pos rfl }

end CommRingₓ

variable {B : Type _} [CommRingₓ B] [IsDomain B] [Field K] {L : Type _} [Field L] [Algebra A K] [IsFractionRing A K]
  {g : A →+* L}

theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) : mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  mk'_eq_iff_eq_mul.2$
    (div_mul_cancel (algebraMap A K r) (IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors hs)).symm

@[simp]
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2

theorem div_surjective (z : K) : ∃ (x y : A)(hy : y ∈ nonZeroDivisors A), algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (nonZeroDivisors A) z
  ⟨x, y, hy,
    by 
      rwa [mk'_eq_div] at h⟩

theorem is_unit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) : IsUnit (g y) :=
  IsUnit.mk0 (g y)$ show g.to_monoid_with_zero_hom y ≠ 0 from g.map_ne_zero_of_mem_non_zero_divisors hg y.2

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : injective g) : K →+* L :=
  lift$ fun y : nonZeroDivisors A => is_unit_map_of_injective hg y

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
theorem lift_algebra_map (hg : injective g) x : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
theorem lift_mk' (hg : injective g) x (y : nonZeroDivisors A) : lift hg (mk' K x y) = g x / g y :=
  by 
    simp only [mk'_eq_div, RingHom.map_div, lift_algebra_map]

/-- Given integral domains `A, B` with fields of fractions `K`, `L`
and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map [Algebra B L] [IsFractionRing B L] {j : A →+* B} (hj : injective j) : K →+* L :=
  map L j (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from fun y hy => j.map_mem_non_zero_divisors hj hy)

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def field_equiv_of_ring_equiv [Algebra B L] [IsFractionRing B L] (h : A ≃+* B) : K ≃+* L :=
  ring_equiv_of_ring_equiv K L h
    (by 
      ext b 
      show b ∈ h.to_equiv '' _ ↔ _ 
      erw [h.to_equiv.image_eq_preimage, Set.Preimage, Set.mem_set_of_eq, mem_non_zero_divisors_iff_ne_zero,
        mem_non_zero_divisors_iff_ne_zero]
      exact h.symm.map_ne_zero_iff)

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integer_normalization_eq_zero_iff
{p : polynomial K} : «expr ↔ »(«expr = »(integer_normalization (non_zero_divisors A) p, 0), «expr = »(p, 0)) :=
begin
  refine [expr polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm],
  obtain ["⟨", "⟨", ident b, ",", ident nonzero, "⟩", ",", ident hb, "⟩", ":=", expr integer_normalization_spec _ p],
  split; intros [ident h, ident i],
  { apply [expr to_map_eq_zero_iff.mp],
    rw ["[", expr hb i, ",", expr h i, "]"] [],
    apply [expr smul_zero],
    assumption },
  { have [ident hi] [] [":=", expr h i],
    rw ["[", expr polynomial.coeff_zero, ",", "<-", expr @to_map_eq_zero_iff A _ K, ",", expr hb i, ",", expr algebra.smul_def, "]"] ["at", ident hi],
    apply [expr or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi)],
    intro [ident h],
    apply [expr mem_non_zero_divisors_iff_ne_zero.mp nonzero],
    exact [expr to_map_eq_zero_iff.mp h] }
end

variable (A K)

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An element of a field is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem is_algebraic_iff
[algebra A L]
[algebra K L]
[is_scalar_tower A K L]
{x : L} : «expr ↔ »(is_algebraic A x, is_algebraic K x) :=
begin
  split; rintros ["⟨", ident p, ",", ident hp, ",", ident px, "⟩"],
  { refine [expr ⟨p.map (algebra_map A K), λ h, hp (polynomial.ext (λ i, _)), _⟩],
    { have [] [":", expr «expr = »(algebra_map A K (p.coeff i), 0)] [":=", expr trans (polynomial.coeff_map _ _).symm (by simp [] [] [] ["[", expr h, "]"] [] [])],
      exact [expr to_map_eq_zero_iff.mp this] },
    { rwa [expr is_scalar_tower.aeval_apply _ K] ["at", ident px] } },
  { exact [expr ⟨integer_normalization _ p, mt integer_normalization_eq_zero_iff.mp hp, integer_normalization_aeval_eq_zero _ p px⟩] }
end

variable {A K}

/-- A field is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
theorem comap_is_algebraic_iff [Algebra A L] [Algebra K L] [IsScalarTower A K L] :
  Algebra.IsAlgebraic A L ↔ Algebra.IsAlgebraic K L :=
  ⟨fun h x => (is_algebraic_iff A K).mp (h x), fun h x => (is_algebraic_iff A K).mpr (h x)⟩

section NumDenom

variable (A) [UniqueFactorizationMonoid A]

theorem exists_reduced_fraction (x : K) :
  ∃ (a : A)(b : nonZeroDivisors A), (∀ {d}, d ∣ a → d ∣ b → IsUnit d) ∧ mk' K a b = x :=
  by 
    obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x 
    obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
      UniqueFactorizationMonoid.exists_reduced_factors' a b (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero)
    obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero 
    refine' ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩
    refine' mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors b_nonzero) _ 
    simp only [Subtype.coe_mk, RingHom.map_mul, Algebra.smul_def] at *
    erw [←hab, mul_assocₓ, mk'_spec' _ a' ⟨b', b'_nonzero⟩]

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def Num (x : K) : A :=
  Classical.some (exists_reduced_fraction A x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : K) : nonZeroDivisors A :=
  Classical.some (Classical.some_spec (exists_reduced_fraction A x))

theorem num_denom_reduced (x : K) : ∀ {d}, d ∣ Num A x → d ∣ denom A x → IsUnit d :=
  (Classical.some_spec (Classical.some_spec (exists_reduced_fraction A x))).1

@[simp]
theorem mk'_num_denom (x : K) : mk' K (Num A x) (denom A x) = x :=
  (Classical.some_spec (Classical.some_spec (exists_reduced_fraction A x))).2

variable {A}

theorem num_mul_denom_eq_num_iff_eq {x y : K} : (x*algebraMap A K (denom A y)) = algebraMap A K (Num A y) ↔ x = y :=
  ⟨fun h =>
      by 
        simpa only [mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
    fun h =>
      eq_mk'_iff_mul_eq.mp
        (by 
          rw [h, mk'_num_denom])⟩

theorem num_mul_denom_eq_num_iff_eq' {x y : K} : (y*algebraMap A K (denom A x)) = algebraMap A K (Num A x) ↔ x = y :=
  ⟨fun h =>
      by 
        simpa only [eq_comm, mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
    fun h =>
      eq_mk'_iff_mul_eq.mp
        (by 
          rw [h, mk'_num_denom])⟩

theorem num_mul_denom_eq_num_mul_denom_iff_eq {x y : K} : ((Num A y*denom A x) = Num A x*denom A y) ↔ x = y :=
  ⟨fun h =>
      by 
        simpa only [mk'_num_denom] using mk'_eq_of_eq h,
    fun h =>
      by 
        rw [h]⟩

theorem eq_zero_of_num_eq_zero {x : K} (h : Num A x = 0) : x = 0 :=
  num_mul_denom_eq_num_iff_eq'.mp
    (by 
      rw [zero_mul, h, RingHom.map_zero])

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integer_of_is_unit_denom {x : K} (h : is_unit (denom A x : A)) : is_integer A x :=
begin
  cases [expr h] ["with", ident d, ident hd],
  have [ident d_ne_zero] [":", expr «expr ≠ »(algebra_map A K (denom A x), 0)] [":=", expr is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors (denom A x).2],
  use [expr «expr * »(«expr↑ »(«expr ⁻¹»(d)), num A x)],
  refine [expr trans _ (mk'_num_denom A x)],
  rw ["[", expr ring_hom.map_mul, ",", expr ring_hom.map_units_inv, ",", expr hd, "]"] [],
  apply [expr mul_left_cancel₀ d_ne_zero],
  rw ["[", "<-", expr mul_assoc, ",", expr mul_inv_cancel d_ne_zero, ",", expr one_mul, ",", expr mk'_spec', "]"] []
end

theorem is_unit_denom_of_num_eq_zero {x : K} (h : Num A x = 0) : IsUnit (denom A x : A) :=
  num_denom_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl

end NumDenom

end IsFractionRing

section Algebra

section IsIntegral

variable {R S} {Rₘ Sₘ : Type _} [CommRingₓ Rₘ] [CommRingₓ Sₘ]

variable [Algebra R Rₘ] [IsLocalization M Rₘ]

variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

section 

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebra_map R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps -/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S) (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
    Rₘ →+* Sₘ).toAlgebra

end 

theorem algebra_map_mk' (r : R) (m : M) :
  (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) (mk' Rₘ r m) =
    mk' Sₘ (algebraMap R S r) ⟨algebraMap R S m, Algebra.mem_algebra_map_submonoid_of_mem m⟩ :=
  map_mk' _ _ _

variable (Rₘ Sₘ)

/-- Injectivity of the underlying `algebra_map` descends to the algebra induced by localization. -/
theorem localization_algebra_injective (hRS : Function.Injective (algebraMap R S))
  (hM : Algebra.algebraMapSubmonoid S M ≤ nonZeroDivisors S) :
  Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  IsLocalization.map_injective_of_injective M Rₘ Sₘ hRS hM

variable {Rₘ Sₘ}

open Polynomial

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_hom.is_integral_elem_localization_at_leading_coeff
{R S : Type*}
[comm_ring R]
[comm_ring S]
(f : «expr →+* »(R, S))
(x : S)
(p : polynomial R)
(hf : «expr = »(p.eval₂ f x, 0))
(M : submonoid R)
(hM : «expr ∈ »(p.leading_coeff, M))
{Rₘ Sₘ : Type*}
[comm_ring Rₘ]
[comm_ring Sₘ]
[algebra R Rₘ]
[is_localization M Rₘ]
[algebra S Sₘ]
[is_localization (M.map f : submonoid S) Sₘ] : (map Sₘ f M.le_comap_map : «expr →+* »(Rₘ, _)).is_integral_elem (algebra_map S Sₘ x) :=
begin
  by_cases [expr triv, ":", expr «expr = »((1 : Rₘ), 0)],
  { exact [expr ⟨0, ⟨trans leading_coeff_zero triv.symm, eval₂_zero _ _⟩⟩] },
  haveI [] [":", expr nontrivial Rₘ] [":=", expr nontrivial_of_ne 1 0 triv],
  obtain ["⟨", ident b, ",", ident hb, "⟩", ":=", expr is_unit_iff_exists_inv.mp (map_units Rₘ ⟨p.leading_coeff, hM⟩)],
  refine [expr ⟨«expr * »(p.map (algebra_map R Rₘ), C b), ⟨_, _⟩⟩],
  { refine [expr monic_mul_C_of_leading_coeff_mul_eq_one _],
    rwa [expr leading_coeff_map_of_leading_coeff_ne_zero (algebra_map R Rₘ)] [],
    refine [expr λ hfp, zero_ne_one (trans (zero_mul b).symm «expr ▸ »(hfp, hb) : «expr = »((0 : Rₘ), 1))] },
  { refine [expr eval₂_mul_eq_zero_of_left _ _ _ _],
    erw ["[", expr eval₂_map, ",", expr is_localization.map_comp, ",", "<-", expr hom_eval₂ _ f (algebra_map S Sₘ) x, "]"] [],
    exact [expr trans (congr_arg (algebra_map S Sₘ) hf) (ring_hom.map_zero _)] }
end

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leading_coeff {x : S} (p : Polynomial R) (hp : aeval x p = 0)
  (hM : p.leading_coeff ∈ M) :
  (map Sₘ (algebraMap R S) (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* _).IsIntegralElem
    (algebraMap S Sₘ x) :=
  (algebraMap R S).is_integral_elem_localization_at_leading_coeff x p hp M hM

-- error in RingTheory.Localization: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem is_integral_localization
(H : algebra.is_integral R S) : (map Sₘ (algebra_map R S) (show «expr ≤ »(_, (algebra.algebra_map_submonoid S M).comap _), from M.le_comap_map) : «expr →+* »(Rₘ, _)).is_integral :=
begin
  intro [ident x],
  by_cases [expr triv, ":", expr «expr = »((1 : R), 0)],
  { have [] [":", expr «expr = »((1 : Rₘ), 0)] [":=", expr by convert [] [expr congr_arg (algebra_map R Rₘ) triv] []; simp [] [] [] [] [] []],
    exact [expr ⟨0, ⟨trans leading_coeff_zero this.symm, eval₂_zero _ _⟩⟩] },
  { haveI [] [":", expr nontrivial R] [":=", expr nontrivial_of_ne 1 0 triv],
    obtain ["⟨", "⟨", ident s, ",", "⟨", ident u, ",", ident hu, "⟩", "⟩", ",", ident hx, "⟩", ":=", expr surj (algebra.algebra_map_submonoid S M) x],
    obtain ["⟨", ident v, ",", ident hv, "⟩", ":=", expr hu],
    obtain ["⟨", ident v', ",", ident hv', "⟩", ":=", expr is_unit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)],
    refine [expr @is_integral_of_is_integral_mul_unit Rₘ _ _ _ (localization_algebra M S) x (algebra_map S Sₘ u) v' _ _],
    { replace [ident hv'] [] [":=", expr congr_arg (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) hv'],
      rw ["[", expr ring_hom.map_mul, ",", expr ring_hom.map_one, ",", "<-", expr ring_hom.comp_apply _ (algebra_map R Rₘ), "]"] ["at", ident hv'],
      erw [expr is_localization.map_comp] ["at", ident hv'],
      exact [expr «expr ▸ »(hv.2, hv')] },
    { obtain ["⟨", ident p, ",", ident hp, "⟩", ":=", expr H s],
      exact [expr «expr ▸ »(hx.symm, is_integral_localization_at_leading_coeff p hp.2 «expr ▸ »(hp.1.symm, M.one_mem))] } }
end

theorem is_integral_localization' {R S : Type _} [CommRingₓ R] [CommRingₓ S] {f : R →+* S} (hf : f.is_integral)
  (M : Submonoid R) : (map (Localization (M.map (f : R →* S))) f M.le_comap_map : Localization M →+* _).IsIntegral :=
  @is_integral_localization R _ M S _ f.to_algebra _ _ _ _ _ _ _ _ hf

end IsIntegral

namespace IsIntegralClosure

variable (A) {L : Type _} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]

variable (C : Type _) [CommRingₓ C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]

variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_algebraic (alg : IsAlgebraic A L) (inj : ∀ x, algebraMap A L x = 0 → x = 0) :
  IsFractionRing C L :=
  { map_units :=
      fun ⟨y, hy⟩ =>
        IsUnit.mk0 _
          (show algebraMap C L y ≠ 0 from
            fun h =>
              mem_non_zero_divisors_iff_ne_zero.mp hy
                ((algebraMap C L).injective_iff.mp (algebra_map_injective C A L) _ h)),
    surj :=
      fun z =>
        let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj
        ⟨⟨mk' C (x : L) x.2, algebraMap _ _ y,
            mem_non_zero_divisors_iff_ne_zero.mpr
              fun h =>
                hy
                  (inj _
                    (by 
                      rw [IsScalarTower.algebra_map_apply A C L, h, RingHom.map_zero]))⟩,
          by 
            rw [SetLike.coe_mk, algebra_map_mk', ←IsScalarTower.algebra_map_apply A C L, hxy]⟩,
    eq_iff_exists :=
      fun x y =>
        ⟨fun h =>
            ⟨1,
              by 
                simpa using algebra_map_injective C A L h⟩,
          fun ⟨c, hc⟩ =>
            congr_argₓ (algebraMap _ L) (mul_right_cancel₀ (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc)⟩ }

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_finite_extension [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
  IsFractionRing C L :=
  is_fraction_ring_of_algebraic A C
    (IsFractionRing.comap_is_algebraic_iff.mpr (is_algebraic_of_finite : IsAlgebraic K L))
    fun x hx =>
      IsFractionRing.to_map_eq_zero_iff.mp
        ((algebraMap K L).map_eq_zero.mp$ (IsScalarTower.algebra_map_apply _ _ _ _).symm.trans hx)

end IsIntegralClosure

namespace integralClosure

variable {L : Type _} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_algebraic [Algebra A L] (alg : IsAlgebraic A L) (inj : ∀ x, algebraMap A L x = 0 → x = 0) :
  IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.is_fraction_ring_of_algebraic A (integralClosure A L) alg inj

variable (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem is_fraction_ring_of_finite_extension [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
  IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.is_fraction_ring_of_finite_extension A K L (integralClosure A L)

end integralClosure

end Algebra

variable (R A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.
-/
@[reducible]
def FractionRing :=
  Localization (nonZeroDivisors R)

namespace FractionRing

variable {A}

noncomputable instance : Field (FractionRing A) :=
  { Localization.commRing, IsFractionRing.toField A with add := ·+·, mul := ·*·, neg := Neg.neg, sub := Sub.sub,
    one := 1, zero := 0, nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul, npow := Localization.npow _ }

@[simp]
theorem mk_eq_div {r s} :
  (Localization.mk r s : FractionRing A) = (algebraMap _ _ r / algebraMap A _ s : FractionRing A) :=
  by 
    rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

variable (A)

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def AlgEquiv (K : Type _) [Field K] [Algebra A K] [IsFractionRing A K] : FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K

end FractionRing

