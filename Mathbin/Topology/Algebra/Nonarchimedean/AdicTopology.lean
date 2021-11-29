import Mathbin.RingTheory.Ideal.Operations 
import Mathbin.Topology.Algebra.Nonarchimedean.Bases 
import Mathbin.Topology.Algebra.UniformRing

/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `is_adic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `with_ideal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `ideal.adic_topology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `ideal.nonarchimedean`: the adic topology is non-archimedean
* `is_ideal_adic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `with_ideal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as a `R`-module.

-/


variable {R : Type _} [CommRingₓ R]

open Set TopologicalAddGroup Submodule Filter

open_locale TopologicalSpace Pointwise

namespace Ideal

theorem adic_basis (I : Ideal R) : SubmodulesRingBasis fun n : ℕ => (I ^ n • ⊤ : Ideal R) :=
  { inter :=
      by 
        suffices  : ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j
        ·
          simpa 
        intro i j 
        exact ⟨max i j, pow_le_pow (le_max_leftₓ i j), pow_le_pow (le_max_rightₓ i j)⟩,
    leftMul :=
      by 
        suffices  : ∀ a : R i : ℕ, ∃ j : ℕ, a • I ^ j ≤ I ^ i
        ·
          simpa 
        intro r n 
        use n 
        rintro a ⟨x, hx, rfl⟩
        exact (I ^ n).smul_mem r hx,
    mul :=
      by 
        suffices  : ∀ i : ℕ, ∃ j : ℕ, («expr↑ » (I ^ j)*«expr↑ » (I ^ j)) ⊆ «expr↑ » (I ^ i)
        ·
          simpa 
        intro n 
        use n 
        rintro a ⟨x, b, hx, hb, rfl⟩
        exact (I ^ n).smul_mem x hb }

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
def RingFilterBasis (I : Ideal R) :=
  I.adic_basis.to_ring_subgroups_basis.to_ring_filter_basis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
def adic_topology (I : Ideal R) : TopologicalSpace R :=
  (adic_basis I).topology

theorem nonarchimedean (I : Ideal R) : @NonarchimedeanRing R _ I.adic_topology :=
  I.adic_basis.to_ring_subgroups_basis.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
theorem has_basis_nhds_zero_adic (I : Ideal R) :
  has_basis (@nhds R I.adic_topology (0 : R)) (fun n : ℕ => True) fun n => ((I ^ n : Ideal R) : Set R) :=
  ⟨by 
      intro U 
      rw [I.ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff]
      split 
      ·
        rintro ⟨-, ⟨i, rfl⟩, h⟩
        replace h : «expr↑ » (I ^ i) ⊆ U :=
          by 
            simpa using h 
        use i, trivialₓ, h
      ·
        rintro ⟨i, -, h⟩
        exact
          ⟨(I ^ i : Ideal R),
            ⟨i,
              by 
                simp ⟩,
            h⟩⟩

-- error in Topology.Algebra.Nonarchimedean.AdicTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_basis_nhds_adic
(I : ideal R)
(x : R) : has_basis (@nhds R I.adic_topology x) (λ
 n : exprℕ(), true) (λ n, «expr '' »(λ y, «expr + »(x, y), («expr ^ »(I, n) : ideal R))) :=
begin
  letI [] [] [":=", expr I.adic_topology],
  have [] [] [":=", expr I.has_basis_nhds_zero_adic.map (λ y, «expr + »(x, y))],
  rwa [expr map_add_left_nhds_zero x] ["at", ident this]
end

variable (I : Ideal R) (M : Type _) [AddCommGroupₓ M] [Module R M]

theorem adic_module_basis : I.ring_filter_basis.submodules_basis fun n : ℕ => I ^ n • (⊤ : Submodule R M) :=
  { inter :=
      fun i j =>
        ⟨max i j,
          le_inf_iff.mpr
            ⟨smul_mono_left$ pow_le_pow (le_max_leftₓ i j), smul_mono_left$ pow_le_pow (le_max_rightₓ i j)⟩⟩,
    smul :=
      fun m i =>
        ⟨(I ^ i • ⊤ : Ideal R), ⟨i, rfl⟩,
          fun a a_in =>
            by 
              replace a_in : a ∈ I ^ i :=
                by 
                  simpa [(I ^ i).mul_top] using a_in 
              exact smul_mem_smul a_in mem_top⟩ }

/-- The topology on a `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adic_module_topology : TopologicalSpace M :=
  @ModuleFilterBasis.topology R M _ I.adic_basis.topology _ _
    (I.ring_filter_basis.module_filter_basis (I.adic_module_basis M))

-- error in Topology.Algebra.Nonarchimedean.AdicTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on a `R`-module `M`, seen as open additive subgroups of `M`. -/
def open_add_subgroup (n : exprℕ()) : @open_add_subgroup R _ I.adic_topology :=
{ is_open' := begin
    letI [] [] [":=", expr I.adic_topology],
    convert [] [expr (I.adic_basis.to_ring_subgroups_basis.open_add_subgroup n).is_open] [],
    simp [] [] [] [] [] []
  end,
  ..«expr ^ »(I, n).to_add_subgroup }

end Ideal

section IsAdic

/-- Given a topology on a ring `R` and an ideal `J`, `is_adic J` means the topology is the
`J`-adic one. -/
def IsAdic [H : TopologicalSpace R] (J : Ideal R) : Prop :=
  H = J.adic_topology

-- error in Topology.Algebra.Nonarchimedean.AdicTopology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
theorem is_adic_iff
[top : topological_space R]
[topological_ring R]
{J : ideal R} : «expr ↔ »(is_adic J, «expr ∧ »(∀
  n : exprℕ(), is_open ((«expr ^ »(J, n) : ideal R) : set R), ∀
  s «expr ∈ » expr𝓝() (0 : R), «expr∃ , »((n : exprℕ()), «expr ⊆ »(((«expr ^ »(J, n) : ideal R) : set R), s)))) :=
begin
  split,
  { intro [ident H],
    change [expr «expr = »(_, _)] [] ["at", ident H],
    rw [expr H] [],
    letI [] [] [":=", expr J.adic_topology],
    split,
    { intro [ident n],
      exact [expr (J.open_add_subgroup n).is_open'] },
    { intros [ident s, ident hs],
      simpa [] [] [] [] [] ["using", expr J.has_basis_nhds_zero_adic.mem_iff.mp hs] } },
  { rintro ["⟨", ident H₁, ",", ident H₂, "⟩"],
    apply [expr topological_add_group.ext],
    { apply [expr @topological_ring.to_topological_add_group] },
    { apply [expr (ring_subgroups_basis.to_ring_filter_basis _).to_add_group_filter_basis.is_topological_add_group] },
    { ext [] [ident s] [],
      letI [] [] [":=", expr ideal.adic_basis J],
      rw [expr J.has_basis_nhds_zero_adic.mem_iff] [],
      split; intro [ident H],
      { rcases [expr H₂ s H, "with", "⟨", ident n, ",", ident h, "⟩"],
        use ["[", expr n, ",", expr trivial, ",", expr h, "]"] },
      { rcases [expr H, "with", "⟨", ident n, ",", "-", ",", ident hn, "⟩"],
        rw [expr mem_nhds_iff] [],
        refine [expr ⟨_, hn, H₁ n, «expr ^ »(J, n).zero_mem⟩] } } }
end

variable [TopologicalSpace R] [TopologicalRing R]

theorem is_ideal_adic_pow {J : Ideal R} (h : IsAdic J) {n : ℕ} (hn : 0 < n) : IsAdic (J ^ n) :=
  by 
    rw [is_adic_iff] at h⊢
    split 
    ·
      intro m 
      rw [←pow_mulₓ]
      apply h.left
    ·
      intro V hV 
      cases' h.right V hV with m hm 
      use m 
      refine' Set.Subset.trans _ hm 
      cases n
      ·
        exfalso 
        exact Nat.not_succ_le_zeroₓ 0 hn 
      rw [←pow_mulₓ, Nat.succ_mul]
      apply Ideal.pow_le_pow 
      apply Nat.le_add_leftₓ

theorem is_bot_adic_iff {A : Type _} [CommRingₓ A] [TopologicalSpace A] [TopologicalRing A] :
  IsAdic (⊥ : Ideal A) ↔ DiscreteTopology A :=
  by 
    rw [is_adic_iff]
    split 
    ·
      rintro ⟨h, h'⟩
      rw [discrete_topology_iff_open_singleton_zero]
      simpa using h 1
    ·
      intros 
      split 
      ·
        simp 
      ·
        intro U U_nhds 
        use 1
        simp [mem_of_mem_nhds U_nhds]

end IsAdic

/-- The ring `R` is equipped with a preferred ideal. -/
class WithIdeal (R : Type _) [CommRingₓ R] where 
  i : Ideal R

namespace WithIdeal

variable (R) [WithIdeal R]

instance (priority := 100) : TopologicalSpace R :=
  I.adicTopology

instance (priority := 100) : NonarchimedeanRing R :=
  RingSubgroupsBasis.nonarchimedean _

instance (priority := 100) : UniformSpace R :=
  TopologicalAddGroup.toUniformSpace R

instance (priority := 100) : UniformAddGroup R :=
  topological_add_group_is_uniform

/-- The adic topology on a `R` module coming from the ideal `with_ideal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
def topological_space_module (M : Type _) [AddCommGroupₓ M] [Module R M] : TopologicalSpace M :=
  (I : Ideal R).adicModuleTopology M

example : NonarchimedeanRing R :=
  by 
    infer_instance

example : TopologicalRing (UniformSpace.Completion R) :=
  by 
    infer_instance

example (M : Type _) [AddCommGroupₓ M] [Module R M] : @TopologicalAddGroup M (WithIdeal.topologicalSpaceModule R M) _ :=
  by 
    infer_instance

example (M : Type _) [AddCommGroupₓ M] [Module R M] :
  @HasContinuousSmul R M _ _ (WithIdeal.topologicalSpaceModule R M) :=
  by 
    infer_instance

example (M : Type _) [AddCommGroupₓ M] [Module R M] :
  @NonarchimedeanAddGroup M _ (WithIdeal.topologicalSpaceModule R M) :=
  SubmodulesBasis.nonarchimedean _

end WithIdeal

