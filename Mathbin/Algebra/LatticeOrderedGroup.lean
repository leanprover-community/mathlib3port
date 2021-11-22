import Mathbin.Algebra.GroupPower.Basic 
import Mathbin.Algebra.Order.Group 
import Mathbin.Tactic.NthRewrite.Default

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
* `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[lattice α]`
* `[comm_group α]`
* `[covariant_class α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/


universe u

@[toAdditive]
instance (priority := 100)LinearOrderedCommGroup.to_covariant_class (α : Type u) [LinearOrderedCommGroup α] :
  CovariantClass α α (·*·) (· ≤ ·) :=
  { elim := fun a b c bc => LinearOrderedCommGroup.mul_le_mul_left _ _ bc a }

variable{α : Type u}[Lattice α][CommGroupₓ α]

/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a ⊔ b) = (c + a) ⊔ (c + b).$$
-/
@[toAdditive]
theorem mul_sup_eq_mul_sup_mul [CovariantClass α α (·*·) (· ≤ ·)] (a b c : α) : (c*a⊔b) = (c*a)⊔c*b :=
  by 
    refine'
      le_antisymmₓ _
        (by 
          simp )
    rw [←mul_le_mul_iff_left (c⁻¹), ←mul_assocₓ, inv_mul_selfₓ, one_mulₓ]
    apply sup_le
    ·
      simp 
    ·
      simp 

/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$-(a ⊔ b)=(-a) ⊓ (-b).$$
-/
@[toAdditive]
theorem inv_sup_eq_inv_inf_inv [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : (a⊔b)⁻¹ = a⁻¹⊓b⁻¹ :=
  by 
    rw [le_antisymm_iffₓ]
    split 
    ·
      rw [le_inf_iff]
      split 
      ·
        rw [inv_le_inv_iff]
        apply le_sup_left
      ·
        rw [inv_le_inv_iff]
        apply le_sup_right
    ·
      rw [←inv_le_inv_iff]
      simp 
      split 
      ·
        rw [←inv_le_inv_iff]
        simp 
      ·
        rw [←inv_le_inv_iff]
        simp 

/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$ -(a ⊓ b) = -a ⊔ -b.$$
-/
@[toAdditive]
theorem inv_inf_eq_sup_inv [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : (a⊓b)⁻¹ = a⁻¹⊔b⁻¹ :=
  by 
    rw [←inv_invₓ (a⁻¹⊔b⁻¹), inv_sup_eq_inv_inf_inv (a⁻¹) (b⁻¹), inv_invₓ, inv_invₓ]

/--
Let `α` be a lattice ordered commutative group. For all elements `a` and `b` in `α`,
$$a ⊓ b + (a ⊔ b) = a + b.$$
-/
@[toAdditive]
theorem inf_mul_sup [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : ((a⊓b)*a⊔b) = a*b :=
  calc ((a⊓b)*a⊔b) = (a⊓b)*(a*b)*b⁻¹⊔a⁻¹ :=
    by 
      rw [mul_sup_eq_mul_sup_mul (b⁻¹) (a⁻¹) (a*b)]
      simp 
    _ = (a⊓b)*(a*b)*(a⊓b)⁻¹ :=
    by 
      rw [inv_inf_eq_sup_inv, sup_comm]
    _ = a*b :=
    by 
      rw [mul_commₓ, inv_mul_cancel_right]
    

namespace LatticeOrderedCommGroup

/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
@[toAdditive Pos
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\n  the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`."]
def mpos (a : α) : α :=
  a⊔1

postfix:1000 "⁺" => mpos

/--
Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,
the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
@[toAdditive neg
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\n  the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`."]
def mneg (a : α) : α :=
  a⁻¹⊔1

postfix:1000 "⁻" => mneg

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$a ≤ |a|.$$
-/
@[toAdditive le_abs]
theorem le_mabs (a : α) : a ≤ |a| :=
  le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`. Then,
$$-a ≤ |a|.$$
-/
@[toAdditive]
theorem inv_le_abs (a : α) : a⁻¹ ≤ |a| :=
  le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
 component `a⁺`. Then `a⁺` is positive.
-/
@[toAdditive pos_pos]
theorem m_pos_pos (a : α) : 1 ≤ a⁺ :=
  le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` withnegative
component `a⁻`. Then `a⁻` is positive.
-/
@[toAdditive neg_pos]
theorem m_neg_pos (a : α) : 1 ≤ a⁻ :=
  le_sup_right

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺`. Then `a⁺` dominates `a`.
-/
@[toAdditive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with negative
component `a⁻`. Then `a⁻` dominates `-a`.
-/
@[toAdditive le_neg]
theorem m_le_neg (a : α) : a⁻¹ ≤ a⁻ :=
  le_sup_left

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the negative
component `a⁻` of `a` is equal to the positive component `(-a)⁺` of `-a`.
-/
@[toAdditive]
theorem neg_eq_pos_inv (a : α) : a⁻ = a⁻¹⁺ :=
  by 
    unfold mneg 
    unfold mpos

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the positive
component `a⁺` of `a` is equal to the negative component `(-a)⁻` of `-a`.
-/
@[toAdditive]
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ :=
  by 
    simp [neg_eq_pos_inv]

/--
Let `α` be a lattice ordered commutative group. For all elements `a`, `b` and `c` in `α`,
$$c + (a ⊓ b) = (c + a) ⊓ (c + b).$$
-/
@[toAdditive]
theorem mul_inf_eq_mul_inf_mul [CovariantClass α α (·*·) (· ≤ ·)] (a b c : α) : (c*a⊓b) = (c*a)⊓c*b :=
  by 
    rw [le_antisymm_iffₓ]
    split 
    ·
      simp 
    ·
      rw [←mul_le_mul_iff_left (c⁻¹), ←mul_assocₓ, inv_mul_selfₓ, one_mulₓ, le_inf_iff]
      simp 

/--
Let `α` be a lattice ordered commutative group with identity `0` and let `a` be an element in `α`
with negative component `a⁻`. Then
$$a⁻ = -(a ⊓ 0).$$
-/
@[toAdditive]
theorem neg_eq_inv_inf_one [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : a⁻ = (a⊓1)⁻¹ :=
  by 
    unfold LatticeOrderedCommGroup.mneg 
    rw [←inv_inj, inv_sup_eq_inv_inf_inv, inv_invₓ, inv_invₓ, one_inv]

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a` can be decomposed as the difference of `a⁺` and
`a⁻`.
-/
@[toAdditive]
theorem pos_inv_neg [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : a = a⁺ / a⁻ :=
  by 
    rw [div_eq_mul_inv]
    apply eq_mul_inv_of_mul_eq 
    unfold LatticeOrderedCommGroup.mneg 
    rw [mul_sup_eq_mul_sup_mul, mul_oneₓ, mul_right_invₓ, sup_comm]
    unfold LatticeOrderedCommGroup.mpos

@[toAdditive, nolint doc_blame_thm]
theorem pos_div_neg' [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : a⁺ / a⁻ = a :=
  (pos_inv_neg _).symm

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with positive
component `a⁺` and negative component `a⁻`. Then `a⁺` and `a⁻` are co-prime (and, since they are
positive, disjoint).
-/
@[toAdditive]
theorem pos_inf_neg_eq_one [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : a⁺⊓a⁻ = 1 :=
  by 
    rw [←mul_right_injₓ (a⁻⁻¹), mul_inf_eq_mul_inf_mul, mul_oneₓ, mul_left_invₓ, mul_commₓ, ←div_eq_mul_inv,
      pos_div_neg', neg_eq_inv_inf_one, inv_invₓ]

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a - b`. Then
$$a⊔b = b + (a - b)⁺.$$
-/
@[toAdditive]
theorem sup_eq_mul_pos_div [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : a⊔b = b*(a / b)⁺ :=
  calc a⊔b = (b*a / b)⊔b*1 :=
    by 
      rw [mul_oneₓ b, div_eq_mul_inv, mul_commₓ a, mul_inv_cancel_left]
    _ = b*a / b⊔1 :=
    by 
      rw [←mul_sup_eq_mul_sup_mul (a / b) 1 b]
    

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α`, and let
`(a - b)⁺` be the positive componet of `a - b`. Then
$$a⊓b = a - (a - b)⁺.$$
-/
@[toAdditive]
theorem inf_eq_div_pos_div [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : a⊓b = a / (a / b)⁺ :=
  calc a⊓b = (a*1)⊓a*b / a :=
    by 
      rw [mul_oneₓ a, div_eq_mul_inv, mul_commₓ b, mul_inv_cancel_left]
    _ = a*1⊓(b / a) :=
    by 
      rw [←mul_inf_eq_mul_inf_mul 1 (b / a) a]
    _ = a*b / a⊓1 :=
    by 
      rw [inf_comm]
    _ = a*(a / b)⁻¹⊓1 :=
    by 
      rw [div_eq_mul_inv]
      nthRw 0[←inv_invₓ b]
      rw [←mul_inv, mul_commₓ (b⁻¹), ←div_eq_mul_inv]
    _ = a*(a / b)⁻¹⊓1⁻¹ :=
    by 
      rw [one_inv]
    _ = a / (a / b⊔1) :=
    by 
      rw [←inv_sup_eq_inv_inf_inv, ←div_eq_mul_inv]
    

/--
Let `α` be a lattice ordered commutative group and let `a` and `b` be elements in `α` with positive
components `a⁺` and `b⁺` and negative components `a⁻` and `b⁻` respectively. Then `b` dominates `a`
if and only if `b⁺` dominates `a⁺` and `a⁻` dominates `b⁻`.
-/
@[toAdditive le_iff_pos_le_neg_ge]
theorem m_le_iff_pos_le_neg_ge [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ :=
  by 
    split 
    ·
      intro h 
      split 
      ·
        apply sup_le (le_transₓ h (LatticeOrderedCommGroup.m_le_pos b)) (LatticeOrderedCommGroup.m_pos_pos b)
      ·
        rw [←inv_le_inv_iff] at h 
        apply sup_le (le_transₓ h (LatticeOrderedCommGroup.m_le_neg a)) (LatticeOrderedCommGroup.m_neg_pos a)
    ·
      intro h 
      rw [←pos_div_neg' a, ←pos_div_neg' b]
      apply div_le_div'' h.1 h.2

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α` with absolute value
`|a|`, positive component `a⁺` and negative component `a⁻`. Then `|a|` decomposes as the sum of `a⁺`
and `a⁻`.
-/
@[toAdditive]
theorem pos_mul_neg [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : |a| = a⁺*a⁻ :=
  by 
    rw [le_antisymm_iffₓ]
    split 
    ·
      unfold HasAbs.abs 
      rw [sup_le_iff]
      split 
      ·
        nthRw 0[←mul_oneₓ a]
        apply mul_le_mul' (LatticeOrderedCommGroup.m_le_pos a) (LatticeOrderedCommGroup.m_neg_pos a)
      ·
        nthRw 0[←one_mulₓ (a⁻¹)]
        apply mul_le_mul' (LatticeOrderedCommGroup.m_pos_pos a) (LatticeOrderedCommGroup.m_le_neg a)
    ·
      have mod_eq_pos : |a|⁺ = |a|
      ·
        nthRw 1[←pos_div_neg' |a|]
        rw [div_eq_mul_inv]
        symm 
        rw [mul_right_eq_self]
        symm 
        rw [one_eq_inv, le_antisymm_iffₓ]
        split 
        ·
          rw [←pos_inf_neg_eq_one a]
          apply le_inf
          ·
            rw [pos_eq_neg_inv]
            apply And.right (Iff.elim_leftₓ (m_le_iff_pos_le_neg_ge _ _) (LatticeOrderedCommGroup.inv_le_abs a))
          ·
            apply And.right (Iff.elim_leftₓ (m_le_iff_pos_le_neg_ge _ _) (LatticeOrderedCommGroup.le_mabs a))
        ·
          apply LatticeOrderedCommGroup.m_neg_pos 
      rw [←inf_mul_sup, pos_inf_neg_eq_one, one_mulₓ, ←mod_eq_pos]
      apply sup_le 
      apply And.left (Iff.elim_leftₓ (m_le_iff_pos_le_neg_ge _ _) (LatticeOrderedCommGroup.le_mabs a))
      rw [neg_eq_pos_inv]
      apply And.left (Iff.elim_leftₓ (m_le_iff_pos_le_neg_ge _ _) (LatticeOrderedCommGroup.inv_le_abs a))

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b - a|`
be the absolute value of `b - a`. Then,
$$a ⊔ b - (a ⊓ b) = |b - a|.$$
-/
@[toAdditive]
theorem sup_div_inf_eq_abs_div [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : (a⊔b) / (a⊓b) = |b / a| :=
  by 
    rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv]
    nthRw 1[div_eq_mul_inv]
    rw [mul_inv_rev, inv_invₓ, mul_commₓ, ←mul_assocₓ, inv_mul_cancel_right, pos_eq_neg_inv (a / b)]
    nthRw 1[div_eq_mul_inv]
    rw [mul_inv_rev, ←div_eq_mul_inv, inv_invₓ, ←pos_mul_neg]

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b - a|`
be the absolute value of `b - a`. Then,
$$2•(a ⊔ b) = a + b + |b - a|.$$
-/
@[toAdditive]
theorem sup_sq_eq_mul_mul_abs_div [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : (a⊔b) ^ 2 = (a*b)*|b / a| :=
  by 
    rw [←inf_mul_sup a b, ←sup_div_inf_eq_abs_div, div_eq_mul_inv, ←mul_assocₓ, mul_commₓ, mul_assocₓ, ←pow_two,
      inv_mul_cancel_leftₓ]

/--
Let `α` be a lattice ordered commutative group, let `a` and `b` be elements in `α` and let `|b-a|`
be the absolute value of `b-a`. Then,
$$2•(a ⊓ b) = a + b - |b - a|.$$
-/
@[toAdditive]
theorem two_inf_eq_mul_div_abs_div [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : (a⊓b) ^ 2 = (a*b) / |b / a| :=
  by 
    rw [←inf_mul_sup a b, ←sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_invₓ, mul_assocₓ,
      mul_inv_cancel_comm_assoc, ←pow_two]

/--
Every lattice ordered commutative group is a distributive lattice
-/
@[toAdditive "Every lattice ordered commutative additive group is a distributive lattice"]
def lattice_ordered_comm_group_to_distrib_lattice (α : Type u) [s : Lattice α] [CommGroupₓ α]
  [CovariantClass α α (·*·) (· ≤ ·)] : DistribLattice α :=
  { s with
    le_sup_inf :=
      by 
        intros 
        rw [←mul_le_mul_iff_left (x⊓(y⊓z)), inf_mul_sup x (y⊓z), ←inv_mul_le_iff_le_mul, le_inf_iff]
        split 
        ·
          rw [inv_mul_le_iff_le_mul, ←inf_mul_sup x y]
          apply mul_le_mul'
          ·
            apply inf_le_inf_left 
            apply inf_le_left
          ·
            apply inf_le_left
        ·
          rw [inv_mul_le_iff_le_mul, ←inf_mul_sup x z]
          apply mul_le_mul'
          ·
            apply inf_le_inf_left 
            apply inf_le_right
          ·
            apply inf_le_right }

/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a ⊔ c - (b ⊔ c)|`, `|a ⊓ c - b ⊓ c|` and `|a - b|` denote the absolute values of
`a ⊔ c - (b ⊔ c)`, `a ⊓ c - b ⊓ c` and `a - b` respectively. Then,
$$|a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|.$$
-/
@[toAdditive]
theorem abs_div_sup_mul_abs_div_inf [CovariantClass α α (·*·) (· ≤ ·)] (a b c : α) :
  (|(a⊔c) / (b⊔c)|*|a⊓c / (b⊓c)|) = |a / b| :=
  by 
    letI this : DistribLattice α := lattice_ordered_comm_group_to_distrib_lattice α 
    calc (|(a⊔c) / (b⊔c)|*|a⊓c / (b⊓c)|) = ((b⊔c⊔(a⊔c)) / ((b⊔c)⊓(a⊔c)))*|a⊓c / (b⊓c)| :=
      by 
        rw [sup_div_inf_eq_abs_div]_ = ((b⊔c⊔(a⊔c)) / ((b⊔c)⊓(a⊔c)))*(b⊓c⊔a⊓c) / (b⊓c⊓(a⊓c)) :=
      by 
        rw [sup_div_inf_eq_abs_div (b⊓c) (a⊓c)]_ = ((b⊔a⊔c) / (b⊓a⊔c))*(b⊔a)⊓c / (b⊓a⊓c) :=
      by 
        rw [←sup_inf_right, ←inf_sup_right, sup_assoc]
        nthRw 1[sup_comm]
        rw [sup_right_idem, sup_assoc, inf_assoc]
        nthRw 3[inf_comm]
        rw [inf_right_idem, inf_assoc]_ = ((b⊔a⊔c)*(b⊔a)⊓c) / (b⊓a⊔c)*b⊓a⊓c :=
      by 
        rw [div_mul_comm]_ = ((b⊔a)*c) / (b⊓a)*c :=
      by 
        rw [mul_commₓ, inf_mul_sup, mul_commₓ (b⊓a⊔c), inf_mul_sup]_ = (b⊔a) / (b⊓a) :=
      by 
        rw [div_eq_mul_inv, mul_inv_rev, mul_assocₓ, mul_inv_cancel_left, ←div_eq_mul_inv]_ = |a / b| :=
      by 
        rw [sup_div_inf_eq_abs_div]

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its positive component `a⁺`.
-/
@[toAdditive pos_pos_id]
theorem m_pos_pos_id (a : α) (h : 1 ≤ a) : a⁺ = a :=
  by 
    unfold LatticeOrderedCommGroup.mpos 
    apply sup_of_le_left h

/--
Let `α` be a lattice ordered commutative group and let `a` be a positive element in `α`. Then `a` is
equal to its absolute value `|a|`.
-/
@[toAdditive abs_pos_eq]
theorem mabs_pos_eq [CovariantClass α α (·*·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : |a| = a :=
  by 
    unfold HasAbs.abs 
    rw [sup_eq_mul_pos_div, div_eq_mul_inv, inv_invₓ, ←pow_two, inv_mul_eq_iff_eq_mul, ←pow_two, m_pos_pos_id]
    rw [pow_two]
    apply one_le_mul h h

/--
Let `α` be a lattice ordered commutative group and let `a` be an element in `α`. Then the absolute
value `|a|` of `a` is positive.
-/
@[toAdditive abs_pos]
theorem mabs_pos [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : 1 ≤ |a| :=
  by 
    rw [pos_mul_neg]
    apply one_le_mul (LatticeOrderedCommGroup.m_pos_pos a) (LatticeOrderedCommGroup.m_neg_pos a)

/--
Let `α` be a lattice ordered commutative group. The unary operation of taking the absolute value is
idempotent.
-/
@[toAdditive abs_idempotent]
theorem mabs_idempotent [CovariantClass α α (·*·) (· ≤ ·)] (a : α) : |a| = ||a|| :=
  by 
    rw [mabs_pos_eq |a|]
    apply LatticeOrderedCommGroup.mabs_pos

/--
Let `α` be a lattice ordered commutative group and let `a`, `b` and `c` be elements in `α`. Let
`|a ⊔ c - (b ⊔ c)|`, `|a ⊓ c - b ⊓ c|` and `|a - b|` denote the absolute values of
`a ⊔ c - (b ⊔ c)`, `a ⊓ c - b ⊓ c` and`a - b` respectively. Then `|a - b|` dominates
`|a ⊔ c - (b ⊔ c)|` and `|a ⊓ c - b ⊓ c|`.
-/
@[toAdditive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [CovariantClass α α (·*·) (· ≤ ·)] (a b c : α) :
  |(a⊔c) / (b⊔c)|⊔|a⊓c / (b⊓c)| ≤ |a / b| :=
  by 
    rw [sup_le_iff]
    split 
    ·
      apply le_of_mul_le_of_one_le_left 
      rw [abs_div_sup_mul_abs_div_inf]
      apply LatticeOrderedCommGroup.mabs_pos
    ·
      apply le_of_mul_le_of_one_le_right 
      rw [abs_div_sup_mul_abs_div_inf]
      apply LatticeOrderedCommGroup.mabs_pos

/--
Let `α` be a lattice ordered commutative group. Then the absolute value satisfies the triangle
inequality.
-/
@[toAdditive abs_triangle]
theorem mabs_triangle [CovariantClass α α (·*·) (· ≤ ·)] (a b : α) : |a*b| ≤ |a|*|b| :=
  by 
    apply sup_le
    ·
      apply mul_le_mul' (LatticeOrderedCommGroup.le_mabs a) (LatticeOrderedCommGroup.le_mabs b)
    ·
      rw [mul_inv]
      apply mul_le_mul' 
      apply LatticeOrderedCommGroup.inv_le_abs 
      apply LatticeOrderedCommGroup.inv_le_abs

end LatticeOrderedCommGroup

