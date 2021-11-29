import Mathbin.RingTheory.Localization 
import Mathbin.RingTheory.Noetherian 
import Mathbin.RingTheory.PrincipalIdealDomain 
import Mathbin.Tactic.FieldSimp

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal S P` is the type of fractional ideals in `P`
 * `has_coe_t (ideal R) (fractional_ideal S P)` instance
 * `comm_semiring (fractional_ideal S P)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal S P)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
 * `fractional_ideal R⁰ K` is the type of fractional ideals in the field of fractions
 * `has_div (fractional_ideal R⁰ K)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `prod_one_self_div_eq` states that `1 / I` is the inverse of `I` if one exists
  * `is_noetherian` states that very fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `is_localization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/


open IsLocalization

open_locale Pointwise

open_locale nonZeroDivisors

section Defs

variable {R : Type _} [CommRingₓ R] {S : Submonoid R} {P : Type _} [CommRingₓ P]

variable [Algebra R P]

variable (S)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def IsFractional (I : Submodule R P) :=
  ∃ (a : _)(_ : a ∈ S), ∀ b _ : b ∈ I, is_integer R (a • b)

variable (S P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }

end Defs

namespace FractionalIdeal

open Set

open Submodule

variable {R : Type _} [CommRingₓ R] {S : Submonoid R} {P : Type _} [CommRingₓ P]

variable [Algebra R P] [loc : IsLocalization S P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coe_to_submodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `is_localization.coe_submodule : ideal R → submodule R P`
(which we use to define `coe : ideal R → fractional_ideal S P`,
referred to as `coe_ideal` in theorem names).
-/
instance : Coe (FractionalIdeal S P) (Submodule R P) :=
  ⟨fun I => I.val⟩

protected theorem IsFractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.prop

section SetLike

instance : SetLike (FractionalIdeal S P) P :=
  { coe := fun I => «expr↑ » (I : Submodule R P), coe_injective' := SetLike.coe_injective.comp Subtype.coe_injective }

@[simp]
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x ∈ (I : Submodule R P) ↔ x ∈ I :=
  Iff.rfl

@[ext]
theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
  SetLike.ext

/-- Copy of a `fractional_ideal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = «expr↑ » p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs,
    by 
      convert p.is_fractional 
      ext 
      simp only [hs]
      rfl⟩

end SetLike

@[simp]
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl

@[simp, normCast]
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) : (Subtype.mk I hI : Submodule R P) = I :=
  rfl

theorem coe_to_submodule_injective : Function.Injective (coeₓ : FractionalIdeal S P → Submodule R P) :=
  Subtype.coe_injective

theorem is_fractional_of_le_one (I : Submodule R P) (h : I ≤ 1) : IsFractional S I :=
  by 
    use 1, S.one_mem 
    intro b hb 
    rw [one_smul]
    obtain ⟨b', b'_mem, rfl⟩ := h hb 
    exact Set.mem_range_self b'

theorem is_fractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I ≤ J) : IsFractional S I :=
  by 
    obtain ⟨a, a_mem, ha⟩ := J.is_fractional 
    use a, a_mem 
    intro b b_mem 
    exact ha b (hIJ b_mem)

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `is_localization.coe_submodule : ideal R → submodule R P`,
which is not to be confused with the `coe : fractional_ideal S P → submodule R P`,
also called `coe_to_submodule` in theorem names.

This map is available as a ring hom, called `fractional_ideal.coe_ideal_hom`.
-/
instance coe_to_fractional_ideal : CoeTₓ (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I =>
      ⟨coe_submodule P I,
        is_fractional_of_le_one _
          (by 
            simpa using coe_submodule_mono P (le_top : I ≤ ⊤))⟩⟩

@[simp, normCast]
theorem coe_coe_ideal (I : Ideal R) : ((I : FractionalIdeal S P) : Submodule R P) = coe_submodule P I :=
  rfl

variable (S)

@[simp]
theorem mem_coe_ideal {x : P} {I : Ideal R} : x ∈ (I : FractionalIdeal S P) ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  mem_coe_submodule _ _

theorem mem_coe_ideal_of_mem {x : R} {I : Ideal R} (hx : x ∈ I) : algebraMap R P x ∈ (I : FractionalIdeal S P) :=
  (mem_coe_ideal S).mpr ⟨x, hx, rfl⟩

theorem coe_ideal_le_coe_ideal' [IsLocalization S P] (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
  (I : FractionalIdeal S P) ≤ J ↔ I ≤ J :=
  coe_submodule_le_coe_submodule h

@[simp]
theorem coe_ideal_le_coe_ideal (K : Type _) [CommRingₓ K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} :
  (I : FractionalIdeal R⁰ K) ≤ J ↔ I ≤ J :=
  IsFractionRing.coe_submodule_le_coe_submodule

instance : HasZero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
theorem mem_zero_iff {x : P} : x ∈ (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ =>
      have x'_eq_zero : x' = 0 := x'_mem_zero 
      by 
        simp [x'_eq_x.symm, x'_eq_zero],
    fun hx =>
      ⟨0, rfl,
        by 
          simp [hx]⟩⟩

variable {S}

@[simp, normCast]
theorem coe_zero : «expr↑ » (0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext$ fun _ => mem_zero_iff S

@[simp, normCast]
theorem coe_to_fractional_ideal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl

variable (P)

include loc

@[simp]
theorem exists_mem_to_map_eq {x : R} {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
  (∃ x', x' ∈ I ∧ algebraMap R P x' = algebraMap R P x) ↔ x ∈ I :=
  ⟨fun ⟨x', hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

variable {P}

theorem coe_to_fractional_ideal_injective (h : S ≤ nonZeroDivisors R) :
  Function.Injective (coeₓ : Ideal R → FractionalIdeal S P) :=
  fun I J heq =>
    have  : ∀ x : R, algebraMap R P x ∈ (I : FractionalIdeal S P) ↔ algebraMap R P x ∈ (J : FractionalIdeal S P) :=
      fun x => HEq ▸ Iff.rfl 
    Ideal.ext
      (by 
        simpa only [mem_coe_ideal, exists_prop, exists_mem_to_map_eq P h] using this)

theorem coe_to_fractional_ideal_eq_zero {I : Ideal R} (hS : S ≤ nonZeroDivisors R) :
  (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  ⟨fun h => coe_to_fractional_ideal_injective hS h,
    fun h =>
      by 
        rw [h, coe_to_fractional_ideal_bot]⟩

theorem coe_to_fractional_ideal_ne_zero {I : Ideal R} (hS : S ≤ nonZeroDivisors R) :
  (I : FractionalIdeal S P) ≠ 0 ↔ I ≠ (⊥ : Ideal R) :=
  not_iff_not.mpr (coe_to_fractional_ideal_eq_zero hS)

omit loc

theorem coe_to_submodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h =>
      coe_to_submodule_injective
        (by 
          simp [h]),
    fun h =>
      by 
        simp [h]⟩

theorem coe_to_submodule_ne_bot {I : FractionalIdeal S P} : «expr↑ » I ≠ (⊥ : Submodule R P) ↔ I ≠ 0 :=
  not_iff_not.mpr coe_to_submodule_eq_bot

instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩

instance : HasOne (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩

variable (S)

@[simp, normCast]
theorem coe_ideal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl

theorem mem_one_iff {x : P} : x ∈ (1 : FractionalIdeal S P) ↔ ∃ x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩

theorem coe_mem_one (x : R) : algebraMap R P x ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨x, rfl⟩

theorem one_mem_one : (1 : P) ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, RingHom.map_one _⟩

variable {S}

/-- `(1 : fractional_ideal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
theorem coe_one_eq_coe_submodule_top : «expr↑ » (1 : FractionalIdeal S P) = coe_submodule P (⊤ : Ideal R) :=
  rfl

@[simp, normCast]
theorem coe_one : («expr↑ » (1 : FractionalIdeal S P) : Submodule R P) = 1 :=
  by 
    rw [coe_one_eq_coe_submodule_top, coe_submodule_top]

section Lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
theorem coe_le_coe {I J : FractionalIdeal S P} : (I : Submodule R P) ≤ (J : Submodule R P) ↔ I ≤ J :=
  Iff.rfl

theorem zero_le (I : FractionalIdeal S P) : 0 ≤ I :=
  by 
    intro x hx 
    convert Submodule.zero_mem _ 
    simpa using hx

instance OrderBot : OrderBot (FractionalIdeal S P) :=
  { bot := 0, bot_le := zero_le }

@[simp]
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl

@[simp]
theorem le_zero_iff {I : FractionalIdeal S P} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff

theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ ∀ x _ : x ∈ I, x = (0 : P) :=
  ⟨fun h x hx =>
      by 
        simpa [h, mem_zero_iff] using hx,
    fun h => le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩

theorem fractional_sup (I J : FractionalIdeal S P) : IsFractional S (I⊔J : Submodule R P) :=
  by 
    rcases I.is_fractional with ⟨aI, haI, hI⟩
    rcases J.is_fractional with ⟨aJ, haJ, hJ⟩
    use aI*aJ 
    use S.mul_mem haI haJ 
    intro b hb 
    rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
    rw [smul_add]
    apply is_integer_add
    ·
      rw [mul_smul, smul_comm]
      exact is_integer_smul (hI bI hbI)
    ·
      rw [mul_smul]
      exact is_integer_smul (hJ bJ hbJ)

theorem fractional_inf (I J : FractionalIdeal S P) : IsFractional S (I⊓J : Submodule R P) :=
  by 
    rcases I.is_fractional with ⟨aI, haI, hI⟩
    use aI 
    use haI 
    intro b hb 
    rcases mem_inf.mp hb with ⟨hbI, hbJ⟩
    exact hI b hbI

instance Lattice : Lattice (FractionalIdeal S P) :=
  { SetLike.partialOrder with inf := fun I J => ⟨I⊓J, fractional_inf I J⟩, sup := fun I J => ⟨I⊔J, fractional_sup I J⟩,
    inf_le_left := fun I J => show (I⊓J : Submodule R P) ≤ I from inf_le_left,
    inf_le_right := fun I J => show (I⊓J : Submodule R P) ≤ J from inf_le_right,
    le_inf := fun I J K hIJ hIK => show (I : Submodule R P) ≤ J⊓K from le_inf hIJ hIK,
    le_sup_left := fun I J => show (I : Submodule R P) ≤ I⊔J from le_sup_left,
    le_sup_right := fun I J => show (J : Submodule R P) ≤ I⊔J from le_sup_right,
    sup_le := fun I J K hIK hJK => show (I⊔J : Submodule R P) ≤ K from sup_le hIK hJK }

instance : SemilatticeSup (FractionalIdeal S P) :=
  { FractionalIdeal.lattice with  }

end Lattice

section Semiringₓ

instance : Add (FractionalIdeal S P) :=
  ⟨·⊔·⟩

@[simp]
theorem sup_eq_add (I J : FractionalIdeal S P) : I⊔J = I+J :=
  rfl

@[simp, normCast]
theorem coe_add (I J : FractionalIdeal S P) : («expr↑ » (I+J) : Submodule R P) = I+J :=
  rfl

@[simp, normCast]
theorem coe_ideal_sup (I J : Ideal R) : «expr↑ » (I⊔J) = (I+J : FractionalIdeal S P) :=
  coe_to_submodule_injective$ coe_submodule_sup _ _ _

theorem fractional_mul (I J : FractionalIdeal S P) : IsFractional S (I*J : Submodule R P) :=
  by 
    rcases I with ⟨I, aI, haI, hI⟩
    rcases J with ⟨J, aJ, haJ, hJ⟩
    use aI*aJ 
    use S.mul_mem haI haJ 
    intro b hb 
    apply Submodule.mul_induction_on hb
    ·
      intro m hm n hn 
      obtain ⟨n', hn'⟩ := hJ n hn 
      rw [mul_smul, mul_commₓ m, ←smul_mul_assoc, ←hn', ←Algebra.smul_def]
      apply hI 
      exact Submodule.smul_mem _ _ hm
    ·
      rw [smul_zero]
      exact ⟨0, RingHom.map_zero _⟩
    ·
      intro x y hx hy 
      rw [smul_add]
      apply is_integer_add hx hy
    ·
      intro r x hx 
      rw [smul_comm]
      exact is_integer_smul hx

/-- `fractional_ideal.mul` is the product of two fractional ideals,
used to define the `has_mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `fractional_ideal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
@[irreducible]
def mul (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I*J, fractional_mul I J⟩

attribute [local semireducible] mul

instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I*J :=
  rfl

@[simp, normCast]
theorem coe_mul (I J : FractionalIdeal S P) : («expr↑ » (I*J) : Submodule R P) = I*J :=
  rfl

@[simp, normCast]
theorem coe_ideal_mul (I J : Ideal R) : («expr↑ » (I*J) : FractionalIdeal S P) = I*J :=
  coe_to_submodule_injective$ coe_submodule_mul _ _ _

theorem mul_left_mono (I : FractionalIdeal S P) : Monotone ((·*·) I) :=
  fun J J' h => mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)

theorem mul_right_mono (I : FractionalIdeal S P) : Monotone fun J => J*I :=
  fun J J' h => mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy

theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) : (i*j) ∈ I*J :=
  Submodule.mul_mem_mul hi hj

theorem mul_le {I J K : FractionalIdeal S P} : (I*J) ≤ K ↔ ∀ i _ : i ∈ I j _ : j ∈ J, (i*j) ∈ K :=
  Submodule.mul_le

@[elab_as_eliminator]
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P → Prop} {r : P} (hr : r ∈ I*J)
  (hm : ∀ i _ : i ∈ I j _ : j ∈ J, C (i*j)) (h0 : C 0) (ha : ∀ x y, C x → C y → C (x+y))
  (hs : ∀ r : R x, C x → C (r • x)) : C r :=
  Submodule.mul_induction_on hr hm h0 ha hs

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance comm_semiring : comm_semiring (fractional_ideal S P) :=
{ add_assoc := λ I J K, sup_assoc,
  add_comm := λ I J, sup_comm,
  add_zero := λ I, sup_bot_eq,
  zero_add := λ I, bot_sup_eq,
  mul_assoc := λ I J K, coe_to_submodule_injective (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, coe_to_submodule_injective (submodule.mul_comm _ _),
  mul_one := λ I, begin
    ext [] [] [],
    split; intro [ident h],
    { apply [expr mul_le.mpr _ h],
      rintros [ident x, ident hx, ident y, "⟨", ident y', ",", ident y'_mem_R, ",", ident rfl, "⟩"],
      convert [] [expr submodule.smul_mem _ y' hx] [],
      rw ["[", expr mul_comm, ",", expr eq_comm, "]"] [],
      exact [expr algebra.smul_def y' x] },
    { have [] [":", expr «expr ∈ »(«expr * »(x, 1), «expr * »(I, 1))] [":=", expr mul_mem_mul h (one_mem_one _)],
      rwa ["[", expr mul_one, "]"] ["at", ident this] }
  end,
  one_mul := λ I, begin
    ext [] [] [],
    split; intro [ident h],
    { apply [expr mul_le.mpr _ h],
      rintros [ident x, "⟨", ident x', ",", ident x'_mem_R, ",", ident rfl, "⟩", ident y, ident hy],
      convert [] [expr submodule.smul_mem _ x' hy] [],
      rw [expr eq_comm] [],
      exact [expr algebra.smul_def x' y] },
    { have [] [":", expr «expr ∈ »(«expr * »(1, x), «expr * »(1, I))] [":=", expr mul_mem_mul (one_mem_one _) h],
      rwa [expr one_mul] ["at", ident this] }
  end,
  mul_zero := λ
  I, eq_zero_iff.mpr (λ
   x
   hx, submodule.mul_induction_on hx (λ
    x
    hx
    y
    hy, by simp [] [] [] ["[", expr (mem_zero_iff S).mp hy, "]"] [] []) rfl (λ
    x
    y
    hx
    hy, by simp [] [] [] ["[", expr hx, ",", expr hy, "]"] [] []) (λ
    r x hx, by simp [] [] [] ["[", expr hx, "]"] [] [])),
  zero_mul := λ
  I, eq_zero_iff.mpr (λ
   x
   hx, submodule.mul_induction_on hx (λ
    x
    hx
    y
    hy, by simp [] [] [] ["[", expr (mem_zero_iff S).mp hx, "]"] [] []) rfl (λ
    x
    y
    hx
    hy, by simp [] [] [] ["[", expr hx, ",", expr hy, "]"] [] []) (λ
    r x hx, by simp [] [] [] ["[", expr hx, "]"] [] [])),
  left_distrib := λ I J K, coe_to_submodule_injective (mul_add _ _ _),
  right_distrib := λ I J K, coe_to_submodule_injective (add_mul _ _ _),
  ..fractional_ideal.has_zero S,
  ..fractional_ideal.has_add,
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_mul }

section Order

theorem add_le_add_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) : (J'+I) ≤ J'+J :=
  sup_le_sup_left hIJ J'

theorem mul_le_mul_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) : (J'*I) ≤ J'*J :=
  mul_le.mpr fun k hk j hj => mul_mem_mul hk (hIJ hj)

theorem le_self_mul_self {I : FractionalIdeal S P} (hI : 1 ≤ I) : I ≤ I*I :=
  by 
    convert mul_left_mono I hI 
    exact (mul_oneₓ I).symm

theorem mul_self_le_self {I : FractionalIdeal S P} (hI : I ≤ 1) : (I*I) ≤ I :=
  by 
    convert mul_left_mono I hI 
    exact (mul_oneₓ I).symm

theorem coe_ideal_le_one {I : Ideal R} : (I : FractionalIdeal S P) ≤ 1 :=
  fun x hx =>
    let ⟨y, _, hy⟩ := (FractionalIdeal.mem_coe_ideal S).mp hx
    (FractionalIdeal.mem_one_iff S).mpr ⟨y, hy⟩

theorem le_one_iff_exists_coe_ideal {J : FractionalIdeal S P} :
  J ≤ (1 : FractionalIdeal S P) ↔ ∃ I : Ideal R, «expr↑ » I = J :=
  by 
    split 
    ·
      intro hJ 
      refine' ⟨⟨{ x:R | algebraMap R P x ∈ J }, _, _, _⟩, _⟩
      ·
        rw [mem_set_of_eq, RingHom.map_zero]
        exact J.val.zero_mem
      ·
        intro a b ha hb 
        rw [mem_set_of_eq, RingHom.map_add]
        exact J.val.add_mem ha hb
      ·
        intro c x hx 
        rw [smul_eq_mul, mem_set_of_eq, RingHom.map_mul, ←Algebra.smul_def]
        exact J.val.smul_mem c hx
      ·
        ext x 
        split 
        ·
          rintro ⟨y, hy, eq_y⟩
          rwa [←eq_y]
        ·
          intro hx 
          obtain ⟨y, eq_x⟩ := (FractionalIdeal.mem_one_iff S).mp (hJ hx)
          rw [←eq_x] at *
          exact ⟨y, hx, rfl⟩
    ·
      rintro ⟨I, hI⟩
      rw [←hI]
      apply coe_ideal_le_one

variable (S P)

/-- `coe_ideal_hom (S : submonoid R) P` is `coe : ideal R → fractional_ideal S P` as a ring hom -/
@[simps]
def coe_ideal_hom : Ideal R →+* FractionalIdeal S P :=
  { toFun := coeₓ, map_add' := coe_ideal_sup, map_mul' := coe_ideal_mul,
    map_one' :=
      by 
        rw [Ideal.one_eq_top, coe_ideal_top],
    map_zero' := coe_to_fractional_ideal_bot }

end Order

variable {P' : Type _} [CommRingₓ P'] [Algebra R P'] [loc' : IsLocalization S P']

variable {P'' : Type _} [CommRingₓ P''] [Algebra R P''] [loc'' : IsLocalization S P'']

theorem fractional_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) : IsFractional S (Submodule.map g.to_linear_map I) :=
  by 
    rcases I with ⟨I, a, a_nonzero, hI⟩
    use a, a_nonzero 
    intro b hb 
    obtain ⟨b', b'_mem, hb'⟩ := submodule.mem_map.mp hb 
    obtain ⟨x, hx⟩ := hI b' b'_mem 
    use x 
    erw [←g.commutes, hx, g.map_smul, hb']

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' :=
  fun I => ⟨Submodule.map g.to_linear_map I, fractional_map g I⟩

@[simp, normCast]
theorem coe_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) : «expr↑ » (map g I) = Submodule.map g.to_linear_map I :=
  rfl

@[simp]
theorem mem_map {I : FractionalIdeal S P} {g : P →ₐ[R] P'} {y : P'} : y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
  Submodule.mem_map

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

@[simp]
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coe_to_submodule_injective (Submodule.map_id I)

@[simp]
theorem map_comp (g' : P' →ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coe_to_submodule_injective (Submodule.map_comp g.to_linear_map g'.to_linear_map I)

@[simp, normCast]
theorem map_coe_ideal (I : Ideal R) : (I : FractionalIdeal S P).map g = I :=
  by 
    ext x 
    simp only [mem_coe_ideal]
    split 
    ·
      rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, (g.commutes y).symm⟩
    ·
      rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩

@[simp]
theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coe_ideal g ⊤

@[simp]
theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coe_ideal g 0

@[simp]
theorem map_add : (I+J).map g = I.map g+J.map g :=
  coe_to_submodule_injective (Submodule.map_sup _ _ _)

@[simp]
theorem map_mul : (I*J).map g = I.map g*J.map g :=
  coe_to_submodule_injective (Submodule.map_mul _ _ _)

@[simp]
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I :=
  by 
    rw [←map_comp, g.symm_comp, map_id]

@[simp]
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
  (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I :=
  by 
    rw [←map_comp, g.comp_symm, map_id]

theorem map_mem_map {f : P →ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
  f x ∈ map f I ↔ x ∈ I :=
  mem_map.trans ⟨fun ⟨x', hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

theorem map_injective (f : P →ₐ[R] P') (h : Function.Injective f) :
  Function.Injective (map f : FractionalIdeal S P → FractionalIdeal S P') :=
  fun I J hIJ =>
    FractionalIdeal.ext fun x => (FractionalIdeal.map_mem_map h).symm.trans (hIJ.symm ▸ FractionalIdeal.map_mem_map h)

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def map_equiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  { toFun := map g, invFun := map g.symm, map_add' := fun I J => map_add I J _, map_mul' := fun I J => map_mul I J _,
    left_inv :=
      fun I =>
        by 
          rw [←map_comp, AlgEquiv.symm_comp, map_id],
    right_inv :=
      fun I =>
        by 
          rw [←map_comp, AlgEquiv.comp_symm, map_id] }

@[simp]
theorem coe_fun_map_equiv (g : P ≃ₐ[R] P') : (map_equiv g : FractionalIdeal S P → FractionalIdeal S P') = map g :=
  rfl

@[simp]
theorem map_equiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : map_equiv g I = map («expr↑ » g) I :=
  rfl

@[simp]
theorem map_equiv_symm (g : P ≃ₐ[R] P') : ((map_equiv g).symm : FractionalIdeal S P' ≃+* _) = map_equiv g.symm :=
  rfl

@[simp]
theorem map_equiv_refl : map_equiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext
    fun x =>
      by 
        simp 

theorem is_fractional_span_iff {s : Set P} :
  IsFractional S (span R s) ↔ ∃ (a : _)(_ : a ∈ S), ∀ b : P, b ∈ s → is_integer R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩,
    fun ⟨a, a_mem, h⟩ =>
      ⟨a, a_mem,
        fun b hb =>
          span_induction hb h
            (by 
              rw [smul_zero]
              exact is_integer_zero)
            (fun x y hx hy =>
              by 
                rw [smul_add]
                exact is_integer_add hx hy)
            fun s x hx =>
              by 
                rw [smul_comm]
                exact is_integer_smul hx⟩⟩

include loc

theorem is_fractional_of_fg {I : Submodule R P} (hI : I.fg) : IsFractional S I :=
  by 
    rcases hI with ⟨I, rfl⟩
    rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
    rw [is_fractional_span_iff]
    exact ⟨s, hs1, hs⟩

omit loc

theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x ∈ I*J) :
  ∃ T T' : Finset P, (T : Set P) ⊆ I ∧ (T' : Set P) ⊆ J ∧ x ∈ span R (T*T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul
    (by 
      simpa using mem_coe.mpr hx)

variable (S)

theorem coe_ideal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
  fg ((I : FractionalIdeal S P) : Submodule R P) ↔ fg I :=
  coe_submodule_fg _ inj _

variable {S}

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fg_unit (I : units (fractional_ideal S P)) : fg (I : submodule R P) :=
begin
  have [] [":", expr «expr ∈ »((1 : P), («expr * »(I, «expr↑ »(«expr ⁻¹»(I))) : fractional_ideal S P))] [],
  { rw [expr units.mul_inv] [],
    exact [expr one_mem_one _] },
  obtain ["⟨", ident T, ",", ident T', ",", ident hT, ",", ident hT', ",", ident one_mem, "⟩", ":=", expr mem_span_mul_finite_of_mem_mul this],
  refine [expr ⟨T, submodule.span_eq_of_le _ hT _⟩],
  rw ["[", "<-", expr one_mul «expr↑ »(I), ",", "<-", expr mul_one (span R «expr↑ »(T)), "]"] [],
  conv_rhs [] [] { rw ["[", "<-", expr fractional_ideal.coe_one, ",", "<-", expr units.mul_inv I, ",", expr fractional_ideal.coe_mul, ",", expr mul_comm «expr↑ »(«expr↑ »(I)), ",", "<-", expr mul_assoc, "]"] },
  refine [expr submodule.mul_le_mul_left (le_trans _ (submodule.mul_le_mul_right (submodule.span_le.mpr hT')))],
  rwa ["[", expr submodule.one_le, ",", expr submodule.span_mul_span, "]"] []
end

theorem fg_of_is_unit (I : FractionalIdeal S P) (h : IsUnit I) : fg (I : Submodule R P) :=
  by 
    rcases h with ⟨I, rfl⟩
    exact fg_unit I

theorem _root_.ideal.fg_of_is_unit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
  (h : IsUnit (I : FractionalIdeal S P)) : I.fg :=
  by 
    rw [←coe_ideal_fg S inj I]
    exact fg_of_is_unit I h

variable (S P P')

include loc loc'

/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'` -/
@[irreducible]
noncomputable def canonical_equiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  map_equiv
    { ring_equiv_of_ring_equiv P P' (RingEquiv.refl R)
        (show S.map _ = S by 
          rw [RingEquiv.to_monoid_hom_refl, Submonoid.map_id]) with
      commutes' := fun r => ring_equiv_of_ring_equiv_eq _ _ }

@[simp]
theorem mem_canonical_equiv_apply {I : FractionalIdeal S P} {x : P'} :
  x ∈ canonical_equiv S P P' I ↔
    ∃ (y : _)(_ : y ∈ I),
      IsLocalization.map P' (RingHom.id R) (fun y hy : y ∈ S => show RingHom.id R y ∈ S from hy) (y : P) = x :=
  by 
    rw [canonical_equiv, map_equiv_apply, mem_map]
    exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
theorem canonical_equiv_symm : (canonical_equiv S P P').symm = canonical_equiv S P' P :=
  RingEquiv.ext$
    fun I =>
      SetLike.ext_iff.mpr$
        fun x =>
          by 
            rw [mem_canonical_equiv_apply, canonical_equiv, map_equiv_symm, map_equiv, RingEquiv.coe_mk, mem_map]
            exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
theorem canonical_equiv_flip I : canonical_equiv S P P' (canonical_equiv S P' P I) = I :=
  by 
    rw [←canonical_equiv_symm, RingEquiv.symm_apply_apply]

end Semiringₓ

section IsFractionRing

/-!
### `is_fraction_ring` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal R⁰ K` where `is_fraction_ring R K`.
-/


variable {K K' : Type _} [Field K] [Field K']

variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']

variable {I J : FractionalIdeal R⁰ K} (h : K →ₐ[R] K')

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Nonzero fractional ideals contain a nonzero integer. -/
theorem exists_ne_zero_mem_is_integer
[nontrivial R]
(hI : «expr ≠ »(I, 0)) : «expr∃ , »((x «expr ≠ » (0 : R)), «expr ∈ »(algebra_map R K x, I)) :=
begin
  obtain ["⟨", ident y, ",", ident y_mem, ",", ident y_not_mem, "⟩", ":=", expr set_like.exists_of_lt (by simpa [] [] ["only"] [] [] ["using", expr bot_lt_iff_ne_bot.mpr hI])],
  have [ident y_ne_zero] [":", expr «expr ≠ »(y, 0)] [":=", expr by simpa [] [] [] [] [] ["using", expr y_not_mem]],
  obtain ["⟨", ident z, ",", "⟨", ident x, ",", ident hx, "⟩", "⟩", ":=", expr exists_integer_multiple «expr ⁰»(R) y],
  refine [expr ⟨x, _, _⟩],
  { rw ["[", expr ne.def, ",", "<-", expr @is_fraction_ring.to_map_eq_zero_iff R _ K, ",", expr hx, ",", expr algebra.smul_def, "]"] [],
    exact [expr mul_ne_zero (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors z.2) y_ne_zero] },
  { rw [expr hx] [],
    exact [expr smul_mem _ _ y_mem] }
end

theorem map_ne_zero [Nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 :=
  by 
    obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_is_integer hI 
    contrapose! x_ne_zero with map_eq_zero 
    refine' is_fraction_ring.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _))
    exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨imp_of_not_imp_not _ _ (map_ne_zero _), fun hI => hI.symm ▸ map_zero h⟩

theorem coe_ideal_injective : Function.Injective (coeₓ : Ideal R → FractionalIdeal R⁰ K) :=
  injective_of_le_imp_le _ fun _ _ => (coe_ideal_le_coe_ideal _).mp

@[simp]
theorem coe_ideal_eq_zero_iff {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  by 
    rw [←coe_to_fractional_ideal_bot]
    exact coe_ideal_injective.eq_iff

theorem coe_ideal_ne_zero_iff {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
  not_iff_not.mpr coe_ideal_eq_zero_iff

theorem coe_ideal_ne_zero {I : Ideal R} (hI : I ≠ ⊥) : (I : FractionalIdeal R⁰ K) ≠ 0 :=
  coe_ideal_ne_zero_iff.mpr hI

end IsFractionRing

section Quotientₓ

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/


open_locale Classical

variable {R₁ : Type _} [CommRingₓ R₁] {K : Type _} [Field K]

variable [Algebra R₁ K] [frac : IsFractionRing R₁ K]

instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1,
      fun h =>
        have this : (1 : K) ∈ (0 : FractionalIdeal R₁⁰ K) :=
          by 
            rw [←(algebraMap R₁ K).map_one]
            simpa only [h] using coe_mem_one R₁⁰ 1
        one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : (I*J) = 1) : I ≠ 0 :=
  fun hI =>
    @zero_ne_one (FractionalIdeal R₁⁰ K) _ _
      (by 
        convert h 
        simp [hI])

variable [IsDomain R₁]

include frac

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fractional_div_of_nonzero
{I J : fractional_ideal «expr ⁰»(R₁) K}
(h : «expr ≠ »(J, 0)) : is_fractional «expr ⁰»(R₁) («expr / »(I, J) : submodule R₁ K) :=
begin
  rcases [expr I, "with", "⟨", ident I, ",", ident aI, ",", ident haI, ",", ident hI, "⟩"],
  rcases [expr J, "with", "⟨", ident J, ",", ident aJ, ",", ident haJ, ",", ident hJ, "⟩"],
  obtain ["⟨", ident y, ",", ident mem_J, ",", ident not_mem_zero, "⟩", ":=", expr set_like.exists_of_lt (by simpa [] [] ["only"] [] [] ["using", expr bot_lt_iff_ne_bot.mpr h])],
  obtain ["⟨", ident y', ",", ident hy', "⟩", ":=", expr hJ y mem_J],
  use [expr «expr * »(aI, y')],
  split,
  { apply [expr (non_zero_divisors R₁).mul_mem haI (mem_non_zero_divisors_iff_ne_zero.mpr _)],
    intro [ident y'_eq_zero],
    have [] [":", expr «expr = »(«expr * »(algebra_map R₁ K aJ, y), 0)] [],
    { rw ["[", "<-", expr algebra.smul_def, ",", "<-", expr hy', ",", expr y'_eq_zero, ",", expr ring_hom.map_zero, "]"] [] },
    have [ident y_zero] [] [":=", expr (mul_eq_zero.mp this).resolve_left (mt ((algebra_map R₁ K).injective_iff.1 (is_fraction_ring.injective _ _) _) (mem_non_zero_divisors_iff_ne_zero.mp haJ))],
    exact [expr not_mem_zero ((mem_zero_iff «expr ⁰»(R₁)).mpr y_zero)] },
  intros [ident b, ident hb],
  convert [] [expr hI _ (hb _ (submodule.smul_mem _ aJ mem_J))] ["using", 1],
  rw ["[", "<-", expr hy', ",", expr mul_comm b, ",", "<-", expr algebra.smul_def, ",", expr mul_smul, "]"] []
end

noncomputable instance fractional_ideal_has_div : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, fractional_div_of_nonzero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K} [J ≠ 0]

@[simp]
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl

theorem div_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) : I / J = ⟨I / J, fractional_div_of_nonzero h⟩ :=
  dif_neg h

@[simp]
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J ≠ 0) :
  («expr↑ » (I / J) : Submodule R₁ K) = «expr↑ » I / («expr↑ » J : Submodule R₁ K) :=
  by 
    unfold Div.div 
    simp only [dif_neg hJ, coe_mk, val_eq_coe]

theorem mem_div_iff_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) {x} : x ∈ I / J ↔ ∀ y _ : y ∈ J, (x*y) ∈ I :=
  by 
    rw [div_nonzero h]
    exact Submodule.mem_div_iff_forall_mul_mem

theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : (I*1 / I) ≤ 1 :=
  by 
    byCases' hI : I = 0
    ·
      rw [hI, div_zero, mul_zero]
      exact zero_le 1
    ·
      rw [←coe_le_coe, coe_mul, coe_div hI, coe_one]
      apply Submodule.mul_one_div_le_one

theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) : I ≤ I*1 / I :=
  by 
    byCases' hI_nz : I = 0
    ·
      rw [hI_nz, div_zero, mul_zero]
      exact zero_le 0
    ·
      rw [←coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
      rw [←coe_le_coe, coe_one] at hI 
      exact Submodule.le_self_mul_one_div hI

theorem le_div_iff_of_nonzero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
  I ≤ J / J' ↔ ∀ x _ : x ∈ I y _ : y ∈ J', (x*y) ∈ J :=
  ⟨fun h x hx => (mem_div_iff_of_nonzero hJ').mp (h hx), fun h x hx => (mem_div_iff_of_nonzero hJ').mpr (h x hx)⟩

theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) : I ≤ J / J' ↔ (I*J') ≤ J :=
  by 
    rw [div_nonzero hJ']
    convert Submodule.le_div_iff_mul_le using 1
    rw [←coe_mul, coe_le_coe]

@[simp]
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I :=
  by 
    rw [div_nonzero (@one_ne_zero (FractionalIdeal R₁⁰ K) _ _)]
    ext 
    split  <;> intro h
    ·
      simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
    ·
      apply mem_div_iff_forall_mul_mem.mpr 
      rintro y ⟨y', _, rfl⟩
      rw [mul_commₓ]
      convert Submodule.smul_mem _ y' h 
      exact (Algebra.smul_def _ _).symm

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_one_div_of_mul_eq_one
(I J : fractional_ideal «expr ⁰»(R₁) K)
(h : «expr = »(«expr * »(I, J), 1)) : «expr = »(J, «expr / »(1, I)) :=
begin
  have [ident hI] [":", expr «expr ≠ »(I, 0)] [":=", expr ne_zero_of_mul_eq_one I J h],
  suffices [ident h'] [":", expr «expr = »(«expr * »(I, «expr / »(1, I)), 1)],
  { exact [expr «expr $ »(congr_arg units.inv, @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl)] },
  apply [expr le_antisymm],
  { apply [expr mul_le.mpr _],
    intros [ident x, ident hx, ident y, ident hy],
    rw [expr mul_comm] [],
    exact [expr (mem_div_iff_of_nonzero hI).mp hy x hx] },
  rw ["<-", expr h] [],
  apply [expr mul_left_mono I],
  apply [expr (le_div_iff_of_nonzero hI).mpr _],
  intros [ident y, ident hy, ident x, ident hx],
  rw [expr mul_comm] [],
  exact [expr mul_mem_mul hx hy]
end

theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : (I*1 / I) = 1 ↔ ∃ J, (I*J) = 1 :=
  ⟨fun h => ⟨1 / I, h⟩,
    fun ⟨J, hJ⟩ =>
      by 
        rwa [←eq_one_div_of_mul_eq_one I J hJ]⟩

variable {K' : Type _} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h :=
  by 
    byCases' H : J = 0
    ·
      rw [H, div_zero, map_zero, div_zero]
    ·
      apply coe_to_submodule_injective 
      simp [div_nonzero H, div_nonzero (map_ne_zero _ H), Submodule.map_div]

@[simp]
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h :=
  by 
    rw [map_div, map_one]

end Quotientₓ

section Field

variable {R₁ K L : Type _} [CommRingₓ R₁] [IsDomain R₁] [Field K] [Field L]

variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 :=
  by 
    rw [or_iff_not_imp_left]
    intro hI 
    simpRw [@SetLike.ext_iff _ _ _ I 1, FractionalIdeal.mem_one_iff]
    intro x 
    split 
    ·
      intro x_mem 
      obtain ⟨n, d, rfl⟩ := IsLocalization.mk'_surjective K⁰ x 
      refine' ⟨n / d, _⟩
      rw [RingHom.map_div, IsFractionRing.mk'_eq_div]
    ·
      rintro ⟨x, rfl⟩
      obtain ⟨y, y_ne, y_mem⟩ := FractionalIdeal.exists_ne_zero_mem_is_integer hI 
      rw [←div_mul_cancel x y_ne, RingHom.map_mul, ←Algebra.smul_def]
      exact Submodule.smul_mem I _ y_mem

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_zero_or_one_of_is_field
(hF : is_field R₁)
(I : fractional_ideal «expr ⁰»(R₁) K) : «expr ∨ »(«expr = »(I, 0), «expr = »(I, 1)) :=
begin
  letI [] [":", expr field R₁] [":=", expr hF.to_field R₁],
  exact [expr @eq_zero_or_one R₁ K _ _ _ (by { unfreezingI { cases [expr _inst_4] [] },
      convert [] [expr _inst_9] [] }) I]
end

end Field

section PrincipalIdealRing

variable {R₁ : Type _} [CommRingₓ R₁] {K : Type _} [Field K]

variable [Algebra R₁ K] [IsFractionRing R₁ K]

open_locale Classical

open Submodule Submodule.IsPrincipal

include loc

theorem is_fractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x 
  is_fractional_span_iff.mpr ⟨a, a.2, fun x' hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

variable (S)

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
@[irreducible]
def span_singleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, is_fractional_span_singleton x⟩

attribute [local semireducible] span_singleton

@[simp]
theorem coe_span_singleton (x : P) : (span_singleton S x : Submodule R P) = span R {x} :=
  rfl

@[simp]
theorem mem_span_singleton {x y : P} : x ∈ span_singleton S y ↔ ∃ z : R, z • y = x :=
  Submodule.mem_span_singleton

theorem mem_span_singleton_self (x : P) : x ∈ span_singleton S x :=
  (mem_span_singleton S).mpr ⟨1, one_smul _ _⟩

variable {S}

theorem eq_span_singleton_of_principal (I : FractionalIdeal S P) [is_principal (I : Submodule R P)] :
  I = span_singleton S (generator (I : Submodule R P)) :=
  coe_to_submodule_injective (span_singleton_generator («expr↑ » I)).symm

theorem is_principal_iff (I : FractionalIdeal S P) : is_principal (I : Submodule R P) ↔ ∃ x, I = span_singleton S x :=
  ⟨fun h => ⟨@generator _ _ _ _ _ («expr↑ » I) h, @eq_span_singleton_of_principal _ _ _ _ _ _ _ I h⟩,
    fun ⟨x, hx⟩ => { principal := ⟨x, trans (congr_argₓ _ hx) (coe_span_singleton _ x)⟩ }⟩

@[simp]
theorem span_singleton_zero : span_singleton S (0 : P) = 0 :=
  by 
    ext 
    simp [Submodule.mem_span_singleton, eq_comm]

theorem span_singleton_eq_zero_iff {y : P} : span_singleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
      span_eq_bot.mp
        (by 
          simpa using congr_argₓ Subtype.val h :
        span R {y} = ⊥)
        y (mem_singleton y),
    fun h =>
      by 
        simp [h]⟩

theorem span_singleton_ne_zero_iff {y : P} : span_singleton S y ≠ 0 ↔ y ≠ 0 :=
  not_congr span_singleton_eq_zero_iff

@[simp]
theorem span_singleton_one : span_singleton S (1 : P) = 1 :=
  by 
    ext 
    refine' (mem_span_singleton S).trans ((exists_congr _).trans (mem_one_iff S).symm)
    intro x' 
    rw [Algebra.smul_def, mul_oneₓ]

@[simp]
theorem span_singleton_mul_span_singleton (x y : P) :
  (span_singleton S x*span_singleton S y) = span_singleton S (x*y) :=
  by 
    apply coe_to_submodule_injective 
    simp only [coe_mul, coe_span_singleton, span_mul_span, singleton_mul_singleton]

@[simp]
theorem coe_ideal_span_singleton (x : R) :
  («expr↑ » (Ideal.span {x} : Ideal R) : FractionalIdeal S P) = span_singleton S (algebraMap R P x) :=
  by 
    ext y 
    refine' (mem_coe_ideal S).trans (Iff.trans _ (mem_span_singleton S).symm)
    split 
    ·
      rintro ⟨y', hy', rfl⟩
      obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hy' 
      use x' 
      rw [smul_eq_mul, RingHom.map_mul, Algebra.smul_def]
    ·
      rintro ⟨y', rfl⟩
      refine' ⟨y'*x, submodule.mem_span_singleton.mpr ⟨y', rfl⟩, _⟩
      rw [RingHom.map_mul, Algebra.smul_def]

@[simp]
theorem canonical_equiv_span_singleton {P'} [CommRingₓ P'] [Algebra R P'] [IsLocalization S P'] (x : P) :
  canonical_equiv S P P' (span_singleton S x) =
    span_singleton S (IsLocalization.map P' (RingHom.id R) (fun y hy : y ∈ S => show RingHom.id R y ∈ S from hy) x) :=
  by 
    apply set_like.ext_iff.mpr 
    intro y 
    split  <;> intro h
    ·
      rw [mem_span_singleton]
      obtain ⟨x', hx', rfl⟩ := (mem_canonical_equiv_apply _ _ _).mp h 
      obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp hx' 
      use z 
      rw [IsLocalization.map_smul]
      rfl
    ·
      rw [mem_canonical_equiv_apply]
      obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp h 
      use z • x 
      use (mem_span_singleton _).mpr ⟨z, rfl⟩
      simp [IsLocalization.map_smul]

theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} :
  (y ∈ span_singleton S x*I) ↔ ∃ (y' : _)(_ : y' ∈ I), y = x*y' :=
  by 
    split 
    ·
      intro h 
      apply FractionalIdeal.mul_induction_on h
      ·
        intro x' hx' y' hy' 
        obtain ⟨a, ha⟩ := (mem_span_singleton S).mp hx' 
        use a • y', Submodule.smul_mem I a hy' 
        rw [←ha, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      ·
        exact ⟨0, Submodule.zero_mem I, (mul_zero x).symm⟩
      ·
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y+y', Submodule.add_mem I hy hy', (mul_addₓ _ _ _).symm⟩
      ·
        rintro r _ ⟨y', hy', rfl⟩
        exact ⟨r • y', Submodule.smul_mem I r hy', (Algebra.mul_smul_comm _ _ _).symm⟩
    ·
      rintro ⟨y', hy', rfl⟩
      exact mul_mem_mul ((mem_span_singleton S).mpr ⟨1, one_smul _ _⟩) hy'

omit loc

variable (K)

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk'_mul_coe_ideal_eq_coe_ideal
{I J : ideal R₁}
{x y : R₁}
(hy : «expr ∈ »(y, «expr ⁰»(R₁))) : «expr ↔ »(«expr = »(«expr * »(span_singleton «expr ⁰»(R₁) (is_localization.mk' K x ⟨y, hy⟩), I), (J : fractional_ideal «expr ⁰»(R₁) K)), «expr = »(«expr * »(ideal.span {x}, I), «expr * »(ideal.span {y}, J))) :=
begin
  have [ident inj] [":", expr function.injective (coe : ideal R₁ → fractional_ideal «expr ⁰»(R₁) K)] [":=", expr fractional_ideal.coe_ideal_injective],
  have [] [":", expr «expr = »(«expr * »(span_singleton «expr ⁰»(R₁) (is_localization.mk' _ (1 : R₁) ⟨y, hy⟩), span_singleton «expr ⁰»(R₁) (algebra_map R₁ K y)), 1)] [],
  { rw ["[", expr span_singleton_mul_span_singleton, ",", expr mul_comm, ",", "<-", expr is_localization.mk'_eq_mul_mk'_one, ",", expr is_localization.mk'_self, ",", expr span_singleton_one, "]"] [] },
  let [ident y'] [":", expr units (fractional_ideal «expr ⁰»(R₁) K)] [":=", expr units.mk_of_mul_eq_one _ _ this],
  have [ident coe_y'] [":", expr «expr = »(«expr↑ »(y'), span_singleton «expr ⁰»(R₁) (is_localization.mk' K (1 : R₁) ⟨y, hy⟩))] [":=", expr rfl],
  refine [expr iff.trans _ (y'.mul_right_inj.trans inj.eq_iff)],
  rw ["[", expr coe_y', ",", expr coe_ideal_mul, ",", expr coe_ideal_span_singleton, ",", expr coe_ideal_mul, ",", expr coe_ideal_span_singleton, ",", "<-", expr mul_assoc, ",", expr span_singleton_mul_span_singleton, ",", "<-", expr mul_assoc, ",", expr span_singleton_mul_span_singleton, ",", expr mul_comm (mk' _ _ _), ",", "<-", expr is_localization.mk'_eq_mul_mk'_one, ",", expr mul_comm (mk' _ _ _), ",", "<-", expr is_localization.mk'_eq_mul_mk'_one, ",", expr is_localization.mk'_self, ",", expr span_singleton_one, ",", expr one_mul, "]"] []
end

variable {K}

theorem span_singleton_mul_coe_ideal_eq_coe_ideal {I J : Ideal R₁} {z : K} :
  (span_singleton R₁⁰ z*(I : FractionalIdeal R₁⁰ K)) = J ↔
    (Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)}*I) = Ideal.span {(IsLocalization.sec R₁⁰ z).2}*J :=
  by 
    erw [←mk'_mul_coe_ideal_eq_coe_ideal K (IsLocalization.sec R₁⁰ z).2.Prop, IsLocalization.mk'_sec K z]

variable [IsDomain R₁]

theorem one_div_span_singleton (x : K) : 1 / span_singleton R₁⁰ x = span_singleton R₁⁰ (x⁻¹) :=
  if h : x = 0 then
    by 
      simp [h]
  else
    (eq_one_div_of_mul_eq_one _ _
        (by 
          simp [h])).symm

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem div_span_singleton
(J : fractional_ideal «expr ⁰»(R₁) K)
(d : K) : «expr = »(«expr / »(J, span_singleton «expr ⁰»(R₁) d), «expr * »(span_singleton «expr ⁰»(R₁) «expr ⁻¹»(d), J)) :=
begin
  rw ["<-", expr one_div_span_singleton] [],
  by_cases [expr hd, ":", expr «expr = »(d, 0)],
  { simp [] [] ["only"] ["[", expr hd, ",", expr span_singleton_zero, ",", expr div_zero, ",", expr zero_mul, "]"] [] [] },
  have [ident h_spand] [":", expr «expr ≠ »(span_singleton «expr ⁰»(R₁) d, 0)] [":=", expr mt span_singleton_eq_zero_iff.mp hd],
  apply [expr le_antisymm],
  { intros [ident x, ident hx],
    rw ["[", "<-", expr mem_coe, ",", expr coe_div h_spand, ",", expr submodule.mem_div_iff_forall_mul_mem, "]"] ["at", ident hx],
    specialize [expr hx d (mem_span_singleton_self «expr ⁰»(R₁) d)],
    have [ident h_xd] [":", expr «expr = »(x, «expr * »(«expr ⁻¹»(d), «expr * »(x, d)))] [],
    { field_simp [] [] [] [] },
    rw ["[", "<-", expr mem_coe, ",", expr coe_mul, ",", expr one_div_span_singleton, ",", expr h_xd, "]"] [],
    exact [expr submodule.mul_mem_mul (mem_span_singleton_self «expr ⁰»(R₁) _) hx] },
  { rw ["[", expr le_div_iff_mul_le h_spand, ",", expr mul_assoc, ",", expr mul_left_comm, ",", expr one_div_span_singleton, ",", expr span_singleton_mul_span_singleton, ",", expr inv_mul_cancel hd, ",", expr span_singleton_one, ",", expr mul_one, "]"] [],
    exact [expr le_refl J] }
end

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_eq_span_singleton_mul
(I : fractional_ideal «expr ⁰»(R₁) K) : «expr∃ , »((a : R₁)
 (aI : ideal R₁), «expr ∧ »(«expr ≠ »(a, 0), «expr = »(I, «expr * »(span_singleton «expr ⁰»(R₁) «expr ⁻¹»(algebra_map R₁ K a), aI)))) :=
begin
  obtain ["⟨", ident a_inv, ",", ident nonzero, ",", ident ha, "⟩", ":=", expr I.is_fractional],
  have [ident nonzero] [] [":=", expr mem_non_zero_divisors_iff_ne_zero.mp nonzero],
  have [ident map_a_nonzero] [":", expr «expr ≠ »(algebra_map R₁ K a_inv, 0)] [":=", expr mt is_fraction_ring.to_map_eq_zero_iff.mp nonzero],
  refine [expr ⟨a_inv, submodule.comap (algebra.linear_map R₁ K) «expr↑ »(«expr * »(span_singleton «expr ⁰»(R₁) (algebra_map R₁ K a_inv), I)), nonzero, ext (λ
     x, iff.trans ⟨_, _⟩ mem_singleton_mul.symm)⟩],
  { intro [ident hx],
    obtain ["⟨", ident x', ",", ident hx', "⟩", ":=", expr ha x hx],
    rw [expr algebra.smul_def] ["at", ident hx'],
    refine [expr ⟨algebra_map R₁ K x', (mem_coe_ideal _).mpr ⟨x', mem_singleton_mul.mpr _, rfl⟩, _⟩],
    { exact [expr ⟨x, hx, hx'⟩] },
    { rw ["[", expr hx', ",", "<-", expr mul_assoc, ",", expr inv_mul_cancel map_a_nonzero, ",", expr one_mul, "]"] [] } },
  { rintros ["⟨", ident y, ",", ident hy, ",", ident rfl, "⟩"],
    obtain ["⟨", ident x', ",", ident hx', ",", ident rfl, "⟩", ":=", expr (mem_coe_ideal _).mp hy],
    obtain ["⟨", ident y', ",", ident hy', ",", ident hx', "⟩", ":=", expr mem_singleton_mul.mp hx'],
    rw [expr algebra.linear_map_apply] ["at", ident hx'],
    rwa ["[", expr hx', ",", "<-", expr mul_assoc, ",", expr inv_mul_cancel map_a_nonzero, ",", expr one_mul, "]"] [] }
end

instance is_principal {R} [CommRingₓ R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K] [IsFractionRing R K]
  (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal :=
  by 
    obtain ⟨a, aI, -, ha⟩ := exists_eq_span_singleton_mul I 
    use algebraMap R K a⁻¹*algebraMap R K (generator aI)
    suffices  : I = span_singleton R⁰ (algebraMap R K a⁻¹*algebraMap R K (generator aI))
    ·
      exact congr_argₓ Subtype.val this 
    convLHS => rw [ha, ←span_singleton_generator aI]
    rw [Ideal.submodule_span_eq, coe_ideal_span_singleton (generator aI), span_singleton_mul_span_singleton]

include loc

theorem le_span_singleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
  (I ≤ span_singleton S x*J) ↔ ∀ zI _ : zI ∈ I, ∃ (zJ : _)(_ : zJ ∈ J), (x*zJ) = zI :=
  show (∀ {zI} hzI : zI ∈ I, zI ∈ span_singleton _ x*J) ↔ ∀ zI _ : zI ∈ I, ∃ (zJ : _)(_ : zJ ∈ J), (x*zJ) = zI by 
    simp only [FractionalIdeal.mem_singleton_mul, eq_comm]

theorem span_singleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
  (span_singleton _ x*I) ≤ J ↔ ∀ z _ : z ∈ I, (x*z) ∈ J :=
  by 
    simp only [FractionalIdeal.mul_le, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_span_singleton]
    split 
    ·
      intro h zI hzI 
      exact h x ⟨1, one_smul _ _⟩ zI hzI
    ·
      rintro h _ ⟨z, rfl⟩ zI hzI 
      rw [Algebra.smul_mul_assoc]
      exact Submodule.smul_mem J.1 _ (h zI hzI)

theorem eq_span_singleton_mul {x : P} {I J : FractionalIdeal S P} :
  (I = span_singleton _ x*J) ↔ (∀ zI _ : zI ∈ I, ∃ (zJ : _)(_ : zJ ∈ J), (x*zJ) = zI) ∧ ∀ z _ : z ∈ J, (x*z) ∈ I :=
  by 
    simp only [le_antisymm_iffₓ, FractionalIdeal.le_span_singleton_mul_iff, FractionalIdeal.span_singleton_mul_le_iff]

end PrincipalIdealRing

variable {R₁ : Type _} [CommRingₓ R₁]

variable {K : Type _} [Field K] [Algebra R₁ K] [frac : IsFractionRing R₁ K]

attribute [local instance] Classical.propDecidable

theorem is_noetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  is_noetherian_submodule.mpr
    fun I hI : I ≤ (0 : FractionalIdeal R₁⁰ K) =>
      by 
        rw [coe_zero] at hI 
        rw [le_bot_iff.mp hI]
        exact fg_bot

theorem is_noetherian_iff {I : FractionalIdeal R₁⁰ K} : IsNoetherian R₁ I ↔ ∀ J _ : J ≤ I, (J : Submodule R₁ K).Fg :=
  is_noetherian_submodule.trans ⟨fun h J hJ => h _ hJ, fun h J hJ => h ⟨J, is_fractional_of_le hJ⟩ hJ⟩

theorem is_noetherian_coe_to_fractional_ideal [_root_.is_noetherian_ring R₁] (I : Ideal R₁) :
  IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) :=
  by 
    rw [is_noetherian_iff]
    intro J hJ 
    obtain ⟨J, rfl⟩ := le_one_iff_exists_coe_ideal.mp (le_transₓ hJ coe_ideal_le_one)
    exact fg_map (IsNoetherian.noetherian J)

include frac

variable [IsDomain R₁]

-- error in RingTheory.FractionalIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_noetherian_span_singleton_inv_to_map_mul
(x : R₁)
{I : fractional_ideal «expr ⁰»(R₁) K}
(hI : is_noetherian R₁ I) : is_noetherian R₁ («expr * »(span_singleton «expr ⁰»(R₁) «expr ⁻¹»(algebra_map R₁ K x), I) : fractional_ideal «expr ⁰»(R₁) K) :=
begin
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { rw ["[", expr hx, ",", expr ring_hom.map_zero, ",", expr _root_.inv_zero, ",", expr span_singleton_zero, ",", expr zero_mul, "]"] [],
    exact [expr is_noetherian_zero] },
  have [ident h_gx] [":", expr «expr ≠ »(algebra_map R₁ K x, 0)] [],
  from [expr mt ((algebra_map R₁ K).injective_iff.mp (is_fraction_ring.injective _ _) x) hx],
  have [ident h_spanx] [":", expr «expr ≠ »(span_singleton «expr ⁰»(R₁) (algebra_map R₁ K x), 0)] [],
  from [expr span_singleton_ne_zero_iff.mpr h_gx],
  rw [expr is_noetherian_iff] ["at", "⊢", ident hI],
  intros [ident J, ident hJ],
  rw ["[", "<-", expr div_span_singleton, ",", expr le_div_iff_mul_le h_spanx, "]"] ["at", ident hJ],
  obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr hI _ hJ],
  use [expr «expr * »(s, {«expr ⁻¹»(algebra_map R₁ K x)})],
  rw ["[", expr finset.coe_mul, ",", expr finset.coe_singleton, ",", "<-", expr span_mul_span, ",", expr hs, ",", "<-", expr coe_span_singleton «expr ⁰»(R₁), ",", "<-", expr coe_mul, ",", expr mul_assoc, ",", expr span_singleton_mul_span_singleton, ",", expr mul_inv_cancel h_gx, ",", expr span_singleton_one, ",", expr mul_one, "]"] []
end

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem IsNoetherian [_root_.is_noetherian_ring R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I :=
  by 
    obtain ⟨d, J, h_nzd, rfl⟩ := exists_eq_span_singleton_mul I 
    apply is_noetherian_span_singleton_inv_to_map_mul 
    apply is_noetherian_coe_to_fractional_ideal

section Adjoin

include loc

omit frac

variable {R P} (S) (x : P) (hx : IsIntegral R x)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
theorem is_fractional_adjoin_integral : IsFractional S (Algebra.adjoin R ({x} : Set P)).toSubmodule :=
  is_fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

/-- `fractional_ideal.adjoin_integral (S : submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
@[simps]
def adjoin_integral : FractionalIdeal S P :=
  ⟨_, is_fractional_adjoin_integral S x hx⟩

theorem mem_adjoin_integral_self : x ∈ adjoin_integral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)

end Adjoin

end FractionalIdeal

