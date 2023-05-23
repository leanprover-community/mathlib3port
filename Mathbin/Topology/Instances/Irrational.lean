/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.instances.irrational
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Irrational
import Mathbin.Data.Rat.Encodable
import Mathbin.Topology.MetricSpace.Baire

/-!
# Topology of irrational numbers

In this file we prove the following theorems:

* `is_Gδ_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational numbers
  form a dense Gδ set;

* `irrational.eventually_forall_le_dist_cast_div`,
  `irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `order_topology`, `no_min_order`, `no_max_order`, and `densely_ordered`
instances for `{x // irrational x}`.

## Tags

irrational, residual
-/


open Set Filter Metric

open Filter Topology

#print isGδ_irrational /-
theorem isGδ_irrational : IsGδ { x | Irrational x } :=
  (countable_range _).isGδ_compl
#align is_Gδ_irrational isGδ_irrational
-/

#print dense_irrational /-
theorem dense_irrational : Dense { x : ℝ | Irrational x } :=
  by
  refine' real.is_topological_basis_Ioo_rat.dense_iff.2 _
  simp only [mem_Union, mem_singleton_iff]
  rintro _ ⟨a, b, hlt, rfl⟩ hne; rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)
#align dense_irrational dense_irrational
-/

#print eventually_residual_irrational /-
theorem eventually_residual_irrational : ∀ᶠ x in residual ℝ, Irrational x :=
  eventually_residual.2 ⟨_, isGδ_irrational, dense_irrational, fun _ => id⟩
#align eventually_residual_irrational eventually_residual_irrational
-/

namespace Irrational

variable {x : ℝ}

instance : OrderTopology { x // Irrational x } :=
  induced_orderTopology _ (fun x y => Iff.rfl) fun x y hlt =>
    let ⟨a, ha, hxa, hay⟩ := exists_irrational_btwn hlt
    ⟨⟨a, ha⟩, hxa, hay⟩

instance : NoMaxOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : ℕ), hx.addNat 1⟩, by simp⟩⟩

instance : NoMinOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : ℕ), hx.subNat 1⟩, by simp⟩⟩

instance : DenselyOrdered { x // Irrational x } :=
  ⟨fun x y hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩

/- warning: irrational.eventually_forall_le_dist_cast_div -> Irrational.eventually_forall_le_dist_cast_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (m : Int), LE.le.{0} Real Real.hasLe ε (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (m : Int), LE.le.{0} Real Real.instLEReal ε (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast m) (Nat.cast.{0} Real Real.natCast n)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align irrational.eventually_forall_le_dist_cast_div Irrational.eventually_forall_le_dist_cast_divₓ'. -/
theorem eventually_forall_le_dist_cast_div (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ m : ℤ, ε ≤ dist x (m / n) :=
  by
  have A : IsClosed (range (fun m => n⁻¹ * m : ℤ → ℝ)) :=
    ((isClosedMap_smul₀ (n⁻¹ : ℝ)).comp int.closed_embedding_coe_real.is_closed_map).closed_range
  have B : x ∉ range (fun m => n⁻¹ * m : ℤ → ℝ) :=
    by
    rintro ⟨m, rfl⟩
    simpa using hx
  rcases Metric.mem_nhds_iff.1 (A.is_open_compl.mem_nhds B) with ⟨ε, ε0, hε⟩
  refine' (ge_mem_nhds ε0).mono fun δ hδ m => not_lt.1 fun hlt => _
  rw [dist_comm] at hlt
  refine' hε (ball_subset_ball hδ hlt) ⟨m, _⟩
  simp [div_eq_inv_mul]
#align irrational.eventually_forall_le_dist_cast_div Irrational.eventually_forall_le_dist_cast_div

/- warning: irrational.eventually_forall_le_dist_cast_div_of_denom_le -> Irrational.eventually_forall_le_dist_cast_div_of_denom_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (k : Nat), (LE.le.{0} Nat Nat.hasLe k n) -> (forall (m : Int), LE.le.{0} Real Real.hasLe ε (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) k))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (k : Nat), (LE.le.{0} Nat instLENat k n) -> (forall (m : Int), LE.le.{0} Real Real.instLEReal ε (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast m) (Nat.cast.{0} Real Real.natCast k))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align irrational.eventually_forall_le_dist_cast_div_of_denom_le Irrational.eventually_forall_le_dist_cast_div_of_denom_leₓ'. -/
theorem eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ k ≤ n, ∀ (m : ℤ), ε ≤ dist x (m / k) :=
  (finite_le_nat n).eventually_all.2 fun k hk => hx.eventually_forall_le_dist_cast_div k
#align irrational.eventually_forall_le_dist_cast_div_of_denom_le Irrational.eventually_forall_le_dist_cast_div_of_denom_le

/- warning: irrational.eventually_forall_le_dist_cast_rat_of_denom_le -> Irrational.eventually_forall_le_dist_cast_rat_of_den_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (r : Rat), (LE.le.{0} Nat Nat.hasLe (Rat.den r) n) -> (LE.le.{0} Real Real.hasLe ε (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) r)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (n : Nat), Filter.Eventually.{0} Real (fun (ε : Real) => forall (r : Rat), (LE.le.{0} Nat instLENat (Rat.den r) n) -> (LE.le.{0} Real Real.instLEReal ε (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x (Rat.cast.{0} Real Real.ratCast r)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align irrational.eventually_forall_le_dist_cast_rat_of_denom_le Irrational.eventually_forall_le_dist_cast_rat_of_den_leₓ'. -/
theorem eventually_forall_le_dist_cast_rat_of_den_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ r : ℚ, r.den ≤ n → ε ≤ dist x r :=
  (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.denom hr r.num
#align irrational.eventually_forall_le_dist_cast_rat_of_denom_le Irrational.eventually_forall_le_dist_cast_rat_of_den_le

end Irrational

