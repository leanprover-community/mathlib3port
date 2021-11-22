import Mathbin.Tactic.Ring 
import Mathbin.Tactic.DocCommands

/-!
# `group`

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/


theorem Tactic.Group.zpow_trick {G : Type _} [Groupₓ G] (a b : G) (n m : ℤ) : ((a*b ^ n)*b ^ m) = a*b ^ n+m :=
  by 
    rw [mul_assocₓ, ←zpow_add]

theorem Tactic.Group.zpow_trick_one {G : Type _} [Groupₓ G] (a b : G) (m : ℤ) : ((a*b)*b ^ m) = a*b ^ m+1 :=
  by 
    rw [mul_assocₓ, mul_self_zpow]

theorem Tactic.Group.zpow_trick_one' {G : Type _} [Groupₓ G] (a b : G) (n : ℤ) : ((a*b ^ n)*b) = a*b ^ n+1 :=
  by 
    rw [mul_assocₓ, mul_zpow_self]

theorem Tactic.Group.zpow_trick_sub {G : Type _} [Groupₓ G] (a b : G) (n m : ℤ) : ((a*b ^ n)*b ^ -m) = a*b ^ (n - m) :=
  by 
    rw [mul_assocₓ, ←zpow_add] <;> rfl

namespace Tactic

setup_tactic_parser

open Tactic.SimpArgType Interactive Tactic.Group

/-- Auxiliary tactic for the `group` tactic. Calls the simplifier only. -/
unsafe def aux_group₁ (locat : loc) : tactic Unit :=
  simp_core {  } skip tt
      [expr (pquote mul_oneₓ), expr (pquote one_mulₓ), expr (pquote one_pow), expr (pquote one_zpow),
        expr (pquote sub_self), expr (pquote add_neg_selfₓ), expr (pquote neg_add_selfₓ), expr (pquote neg_negₓ),
        expr (pquote tsub_self), expr (pquote Int.coe_nat_add), expr (pquote Int.coe_nat_mul),
        expr (pquote Int.coe_nat_zero), expr (pquote Int.coe_nat_one), expr (pquote Int.coe_nat_bit0),
        expr (pquote Int.coe_nat_bit1), expr (pquote Int.mul_neg_eq_neg_mul_symm),
        expr (pquote Int.neg_mul_eq_neg_mul_symm), symm_expr (pquote zpow_coe_nat), symm_expr (pquote zpow_neg_one),
        symm_expr (pquote zpow_mul), symm_expr (pquote zpow_add_one), symm_expr (pquote zpow_one_add),
        symm_expr (pquote zpow_add), expr (pquote mul_zpow_neg_one), expr (pquote zpow_zero), expr (pquote mul_zpow),
        symm_expr (pquote mul_assocₓ), expr (pquote zpow_trick), expr (pquote zpow_trick_one),
        expr (pquote zpow_trick_one'), expr (pquote zpow_trick_sub), expr (pquote Tactic.Ring.hornerₓ)]
      [] locat >>
    skip

/-- Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents. -/
unsafe def aux_group₂ (locat : loc) : tactic Unit :=
  ring_nf none Tactic.Ring.NormalizeMode.raw locat

end Tactic

namespace Tactic.Interactive

setup_tactic_parser

open Tactic

/--
Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```
-/
unsafe def Groupₓ (locat : parse location) : tactic Unit :=
  do 
    when locat.include_goal sorry 
    try (aux_group₁ locat)
    repeat (aux_group₂ locat; aux_group₁ locat)

end Tactic.Interactive

add_tactic_doc
  { Name := "group", category := DocCategory.tactic, declNames := [`tactic.interactive.group],
    tags := ["decision procedure", "simplification"] }

