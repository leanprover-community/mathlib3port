import Mathbin.Algebra.Group.Conj
import Mathbin.GroupTheory.GroupAction.ConjAct

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `comm_prob`: The commuting probability of a finite type with a multiplication operation.

## Todo
* Neumann's theorem.
-/


noncomputable section

open_locale Classical

open_locale BigOperators

open Fintype

variable (M : Type _) [Fintype M] [Mul M]

/-- The commuting probability of a finite type with a multiplication operation -/
def commProb : ℚ :=
  card { p : M × M // p.1 * p.2 = p.2 * p.1 } / card M ^ 2

theorem comm_prob_def : commProb M = card { p : M × M // p.1 * p.2 = p.2 * p.1 } / card M ^ 2 :=
  rfl

theorem comm_prob_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x => div_pos (Nat.cast_pos.mpr (card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩)) (pow_pos (Nat.cast_pos.mpr card_pos) 2)

theorem comm_prob_le_one : commProb M ≤ 1 := by
  refine' div_le_one_of_le _ (sq_nonneg (card M))
  rw [← Nat.cast_pow, Nat.cast_le, sq, ← card_prod]
  apply set_fintype_card_le_univ

theorem comm_prob_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ Commutative (· * · : M → M → M) := by
  change (card { p : M × M | p.1 * p.2 = p.2 * p.1 } : ℚ) / _ = 1 ↔ _
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod, set_fintype_card_eq_univ_iff,
    Set.eq_univ_iff_forall]
  · exact ⟨fun h x y => h (x, y), fun h x => h x.1 x.2⟩
    
  · exact pow_ne_zero 2 (nat.cast_ne_zero.mpr card_ne_zero)
    

variable (G : Type _) [Groupₓ G] [Fintype G]

theorem card_comm_eq_card_conj_classes_mul_card :
    card { p : G × G // p.1 * p.2 = p.2 * p.1 } = card (ConjClasses G) * card G :=
  calc
    card { p : G × G // p.1 * p.2 = p.2 * p.1 } = card (Σ g, { h // g * h = h * g }) :=
      card_congr (Equivₓ.subtypeProdEquivSigmaSubtype fun g h : G => g * h = h * g)
    _ = ∑ g, card { h // g * h = h * g } := card_sigma _
    _ = ∑ g, card (MulAction.FixedBy (ConjAct G) G g) :=
      sum_equiv ConjAct.toConjAct.toEquiv _ _ fun g =>
        card_congr' $ congr_argₓ _ $ funext $ fun h => mul_inv_eq_iff_eq_mul.symm.to_eq
    _ = card (Quotientₓ (MulAction.orbitRel (ConjAct G) G)) * card G :=
      MulAction.sum_card_fixed_by_eq_card_orbits_mul_card_group (ConjAct G) G
    _ = card (Quotientₓ (IsConj.setoid G)) * card G := by
      have this : MulAction.orbitRel (ConjAct G) G = IsConj.setoid G :=
        Setoidₓ.ext fun g h => (Setoidₓ.comm' _).trans is_conj_iff.symm
      cc
    

theorem comm_prob_def' : commProb G = card (ConjClasses G) / card G := by
  rw [commProb, card_comm_eq_card_conj_classes_mul_card, Nat.cast_mul, sq]
  exact mul_div_mul_right (card (ConjClasses G)) (card G) (nat.cast_ne_zero.mpr card_ne_zero)

