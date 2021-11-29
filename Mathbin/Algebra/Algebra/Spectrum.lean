import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.

## Main statements

* `smul_eq_smul`: units in the scalar ring commute (multiplication) with the spectrum.
* `left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `units_mem_mul_iff_mem_swap_mul` and `preimage_units_mul_eq_swap_mul`: the units
  (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.

## Notations

* `σ a` : `spectrum R a` of `a : A`

## TODO

* Prove the *spectral mapping theorem* for the polynomial functional calculus
-/


universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommRingₓ R] [Ringₓ A] [Algebra R A]

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
def Resolvent (a : A) : Set R :=
  { r:R | IsUnit (algebraMap R A r - a) }

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent.  -/
def Spectrum (a : A) : Set R :=
  «expr ᶜ» (Resolvent R a)

end Defs

variable {R : Type u} {A : Type v}

variable [CommRingₓ R] [Ringₓ A] [Algebra R A]

-- error in Algebra.Algebra.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_unit.smul_sub_iff_sub_inv_smul
{r : units R}
{a : A} : «expr ↔ »(is_unit «expr - »(«expr • »(r, 1), a), is_unit «expr - »(1, «expr • »(«expr ⁻¹»(r), a))) :=
begin
  have [ident a_eq] [":", expr «expr = »(a, «expr • »(r, «expr • »(«expr ⁻¹»(r), a)))] [],
  by simp [] [] [] [] [] [],
  nth_rewrite [0] [expr a_eq] [],
  rw ["[", "<-", expr smul_sub, ",", expr is_unit_smul_iff, "]"] []
end

namespace Spectrum

local notation "σ" => Spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

theorem not_mem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) :=
  by 
    apply not_iff_not.mp 
    simp [Set.not_not_mem, mem_iff]

theorem mem_resolvent_of_left_right_inverse {r : R} {a b c : A} (h₁ : ((↑ₐ r - a)*b) = 1) (h₂ : (c*↑ₐ r - a) = 1) :
  r ∈ Resolvent R a :=
  Units.is_unit
    ⟨↑ₐ r - a, b, h₁,
      by 
        rwa [←left_inv_eq_right_invₓ h₂ h₁]⟩

theorem mem_resolvent_iff {r : R} {a : A} : r ∈ Resolvent R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

-- error in Algebra.Algebra.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_mem_iff
{a : A}
{r s : R} : «expr ↔ »(«expr ∈ »(r, exprσ() a), «expr ∈ »(«expr + »(r, s), exprσ() «expr + »(«expr↑ₐ»() s, a))) :=
begin
  apply [expr not_iff_not.mpr],
  simp [] [] ["only"] ["[", expr mem_resolvent_iff, "]"] [] [],
  have [ident h_eq] [":", expr «expr = »(«expr - »(«expr↑ₐ»() «expr + »(r, s), «expr + »(«expr↑ₐ»() s, a)), «expr - »(«expr↑ₐ»() r, a))] [],
  { simp [] [] [] [] [] [],
    noncomm_ring },
  rw [expr h_eq] []
end

-- error in Algebra.Algebra.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem smul_mem_smul_iff
{a : A}
{s : R}
{r : units R} : «expr ↔ »(«expr ∈ »(«expr • »(r, s), exprσ() «expr • »(r, a)), «expr ∈ »(s, exprσ() a)) :=
begin
  apply [expr not_iff_not.mpr],
  simp [] [] ["only"] ["[", expr mem_resolvent_iff, ",", expr algebra.algebra_map_eq_smul_one, "]"] [] [],
  have [ident h_eq] [":", expr «expr = »(«expr • »(«expr • »(r, s), (1 : A)), «expr • »(r, «expr • »(s, 1)))] [],
  by simp [] [] [] [] [] [],
  rw ["[", expr h_eq, ",", "<-", expr smul_sub, ",", expr is_unit_smul_iff, "]"] []
end

open_locale Pointwise

-- error in Algebra.Algebra.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem smul_eq_smul (a : A) (r : units R) : «expr = »(exprσ() «expr • »(r, a), «expr • »(r, exprσ() a)) :=
begin
  ext [] [] [],
  have [ident x_eq] [":", expr «expr = »(x, «expr • »(r, «expr • »(«expr ⁻¹»(r), x)))] [],
  by simp [] [] [] [] [] [],
  nth_rewrite [0] [expr x_eq] [],
  rw [expr smul_mem_smul_iff] [],
  split,
  { exact [expr λ h, ⟨«expr • »(«expr ⁻¹»(r), x), ⟨h, by simp [] [] [] [] [] []⟩⟩] },
  { rintros ["⟨", "_", ",", "_", ",", ident x'_eq, "⟩"],
    simpa [] [] [] ["[", "<-", expr x'_eq, "]"] [] [] }
end

theorem left_add_coset_eq (a : A) (r : R) : LeftAddCoset r (σ a) = σ (↑ₐ r+a) :=
  by 
    ext 
    rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff]
    nthRw 1[←sub_add_cancel x r]

-- error in Algebra.Algebra.Spectrum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unit_mem_mul_iff_mem_swap_mul
{a b : A}
{r : units R} : «expr ↔ »(«expr ∈ »(«expr↑ »(r), exprσ() «expr * »(a, b)), «expr ∈ »(«expr↑ »(r), exprσ() «expr * »(b, a))) :=
begin
  apply [expr not_iff_not.mpr],
  simp [] [] ["only"] ["[", expr mem_resolvent_iff, ",", expr algebra.algebra_map_eq_smul_one, "]"] [] [],
  have [ident coe_smul_eq] [":", expr «expr = »(«expr • »(«expr↑ »(r), 1), «expr • »(r, (1 : A)))] [],
  from [expr rfl],
  rw [expr coe_smul_eq] [],
  simp [] [] ["only"] ["[", expr is_unit.smul_sub_iff_sub_inv_smul, "]"] [] [],
  have [ident right_inv_of_swap] [":", expr ∀
   {x y z : A}
   (h : «expr = »(«expr * »(«expr - »(1, «expr * »(x, y)), z), 1)), «expr = »(«expr * »(«expr - »(1, «expr * »(y, x)), «expr + »(1, «expr * »(«expr * »(y, z), x))), 1)] [],
  from [expr λ x y z h, calc
     «expr = »(«expr * »(«expr - »(1, «expr * »(y, x)), «expr + »(1, «expr * »(«expr * »(y, z), x))), «expr + »(«expr - »(1, «expr * »(y, x)), «expr * »(«expr * »(y, «expr * »(«expr - »(1, «expr * »(x, y)), z)), x))) : by noncomm_ring
     «expr = »(..., 1) : by simp [] [] [] ["[", expr h, "]"] [] []],
  have [ident left_inv_of_swap] [":", expr ∀
   {x y z : A}
   (h : «expr = »(«expr * »(z, «expr - »(1, «expr * »(x, y))), 1)), «expr = »(«expr * »(«expr + »(1, «expr * »(«expr * »(y, z), x)), «expr - »(1, «expr * »(y, x))), 1)] [],
  from [expr λ x y z h, calc
     «expr = »(«expr * »(«expr + »(1, «expr * »(«expr * »(y, z), x)), «expr - »(1, «expr * »(y, x))), «expr + »(«expr - »(1, «expr * »(y, x)), «expr * »(«expr * »(y, «expr * »(z, «expr - »(1, «expr * »(x, y)))), x))) : by noncomm_ring
     «expr = »(..., 1) : by simp [] [] [] ["[", expr h, "]"] [] []],
  have [ident is_unit_one_sub_mul_of_swap] [":", expr ∀
   {x y : A}
   (h : is_unit «expr - »(1, «expr * »(x, y))), is_unit «expr - »(1, «expr * »(y, x))] [],
  from [expr λ x y h, by { let [ident h₁] [] [":=", expr right_inv_of_swap h.unit.val_inv],
     let [ident h₂] [] [":=", expr left_inv_of_swap h.unit.inv_val],
     exact [expr ⟨⟨«expr - »(1, «expr * »(y, x)), «expr + »(1, «expr * »(«expr * »(y, h.unit.inv), x)), h₁, h₂⟩, rfl⟩] }],
  have [ident is_unit_one_sub_mul_iff_swap] [":", expr ∀
   {x y : A}, «expr ↔ »(is_unit «expr - »(1, «expr * »(x, y)), is_unit «expr - »(1, «expr * »(y, x)))] [],
  by { intros [],
    split,
    repeat { apply [expr is_unit_one_sub_mul_of_swap] } },
  rw ["[", "<-", expr smul_mul_assoc, ",", "<-", expr mul_smul_comm «expr ⁻¹»(r) b a, ",", expr is_unit_one_sub_mul_iff_swap, "]"] []
end

theorem preimage_units_mul_eq_swap_mul {a b : A} : (coeₓ : Units R → R) ⁻¹' σ (a*b) = coeₓ ⁻¹' σ (b*a) :=
  by 
    ext 
    exact unit_mem_mul_iff_mem_swap_mul

end Spectrum

