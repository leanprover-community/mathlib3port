import Mathbin.Topology.Algebra.Nonarchimedean.Basic 
import Mathbin.Topology.Algebra.FilterBasis 
import Mathbin.Algebra.Module.SubmodulePointwise

/-!
# Neighborhood bases for non-archimedean rings and modules

This files contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `ring_subgroups_basis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`ring_subgroups_basis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular the given subgroups become open subgroups
(bundled in `ring_subgroups_basis.open_add_subgroup`) and we get a non-archimedean topological ring
(`ring_subgroups_basis.nonarchimedean`).

A special case of this construction is given by `submodules_basis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rises to the adic topology
(studied in its own file).

-/


open Set Filter Function Lattice AddGroupWithZeroNhd

open_locale TopologicalSpace Filter Pointwise

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure ring_subgroups_basis
{A ι : Type*}
[ring A]
(B : ι → add_subgroup A) : exprProp() :=
  (inter : ∀ i j, «expr∃ , »((k), «expr ≤ »(B k, «expr ⊓ »(B i, B j))))
  (mul : ∀ i, «expr∃ , »((j), «expr ⊆ »(«expr * »((B j : set A), B j), B i)))
  (left_mul : ∀ x : A, ∀ i, «expr∃ , »((j), «expr ⊆ »((B j : set A), «expr ⁻¹' »(λ y : A, «expr * »(x, y), B i))))
  (right_mul : ∀ x : A, ∀ i, «expr∃ , »((j), «expr ⊆ »((B j : set A), «expr ⁻¹' »(λ y : A, «expr * »(y, x), B i))))

namespace RingSubgroupsBasis

variable{A ι : Type _}[Ringₓ A]

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem of_comm
{A ι : Type*}
[comm_ring A]
(B : ι → add_subgroup A)
(inter : ∀ i j, «expr∃ , »((k), «expr ≤ »(B k, «expr ⊓ »(B i, B j))))
(mul : ∀ i, «expr∃ , »((j), «expr ⊆ »(«expr * »((B j : set A), B j), B i)))
(left_mul : ∀
 x : A, ∀
 i, «expr∃ , »((j), «expr ⊆ »((B j : set A), «expr ⁻¹' »(λ y : A, «expr * »(x, y), B i)))) : ring_subgroups_basis B :=
{ inter := inter,
  mul := mul,
  left_mul := left_mul,
  right_mul := begin
    intros [ident x, ident i],
    cases [expr left_mul x i] ["with", ident j, ident hj],
    use [expr j],
    simpa [] [] [] ["[", expr mul_comm, "]"] [] ["using", expr hj]
  end }

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
def to_ring_filter_basis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) : RingFilterBasis A :=
  { Sets := { U | ∃ i, U = B i },
    Nonempty :=
      by 
        inhabit ι 
        exact ⟨B (default ι), default ι, rfl⟩,
    inter_sets :=
      by 
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        cases' hB.inter i j with k hk 
        use B k, k, rfl, hk,
    zero' :=
      by 
        rintro _ ⟨i, rfl⟩
        exact (B i).zero_mem,
    add' :=
      by 
        rintro _ ⟨i, rfl⟩
        use B i, i, rfl 
        rintro x ⟨y, z, y_in, z_in, rfl⟩
        exact (B i).add_mem y_in z_in,
    neg' :=
      by 
        rintro _ ⟨i, rfl⟩
        use B i, i, rfl 
        intro x x_in 
        exact (B i).neg_mem x_in,
    conj' :=
      by 
        rintro x₀ _ ⟨i, rfl⟩
        use B i, i, rfl 
        simp ,
    mul' :=
      by 
        rintro _ ⟨i, rfl⟩
        cases' hB.mul i with k hk 
        use B k, k, rfl, hk,
    mul_left' :=
      by 
        rintro x₀ _ ⟨i, rfl⟩
        cases' hB.left_mul x₀ i with k hk 
        use B k, k, rfl, hk,
    mul_right' :=
      by 
        rintro x₀ _ ⟨i, rfl⟩
        cases' hB.right_mul x₀ i with k hk 
        use B k, k, rfl, hk }

variable[Nonempty ι]{B : ι → AddSubgroup A}(hB : RingSubgroupsBasis B)

theorem mem_add_group_filter_basis_iff {V : Set A} :
  V ∈ hB.to_ring_filter_basis.to_add_group_filter_basis ↔ ∃ i, V = B i :=
  Iff.rfl

theorem mem_add_group_filter_basis i : (B i : Set A) ∈ hB.to_ring_filter_basis.to_add_group_filter_basis :=
  ⟨i, rfl⟩

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
def topology : TopologicalSpace A :=
  hB.to_ring_filter_basis.to_add_group_filter_basis.topology

theorem has_basis_nhds_zero : has_basis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by 
      intro s 
      rw [hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff]
      split 
      ·
        rintro ⟨-, ⟨i, rfl⟩, hi⟩
        exact ⟨i, trivialₓ, hi⟩
      ·
        rintro ⟨i, -, hi⟩
        exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩

theorem has_basis_nhds (a : A) : has_basis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by 
      intro s 
      rw [(hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff]
      simp only [exists_prop, exists_true_left]
      split 
      ·
        rintro ⟨-, ⟨i, rfl⟩, hi⟩
        use i 
        convert hi 
        ext b 
        split 
        ·
          intro h 
          use b - a, h 
          abel
        ·
          rintro ⟨c, hc, rfl⟩
          simpa using hc
      ·
        rintro ⟨i, hi⟩
        use B i, i, rfl 
        rw [image_subset_iff]
        rintro b b_in 
        apply hi 
        simpa using b_in⟩

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/ def open_add_subgroup (i : ι) : @open_add_subgroup A _ hB.topology :=
{ is_open' := begin
    letI [] [] [":=", expr hB.topology],
    rw [expr is_open_iff_mem_nhds] [],
    intros [ident a, ident a_in],
    rw [expr (hB.has_basis_nhds a).mem_iff] [],
    use ["[", expr i, ",", expr trivial, "]"],
    rintros [ident b, ident b_in],
    simpa [] [] [] [] [] ["using", expr (B i).add_mem a_in b_in]
  end,
  ..B i }

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nonarchimedean : @nonarchimedean_ring A _ hB.topology :=
begin
  letI [] [] [":=", expr hB.topology],
  constructor,
  intros [ident U, ident hU],
  obtain ["⟨", ident i, ",", "-", ",", ident hi, ":", expr «expr ⊆ »((B i : set A), U), "⟩", ":=", expr hB.has_basis_nhds_zero.mem_iff.mp hU],
  exact [expr ⟨hB.open_add_subgroup i, hi⟩]
end

end RingSubgroupsBasis

variable{ι R A : Type _}[CommRingₓ R][CommRingₓ A][Algebra R A]

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesRingBasis(B : ι → Submodule R A) : Prop where 
  inter : ∀ i j, ∃ k, B k ≤ B i⊓B j 
  leftMul : ∀ (a : A) i, ∃ j, a • B j ≤ B i 
  mul : ∀ i, ∃ j, ((B j : Set A)*B j) ⊆ B i

namespace SubmodulesRingBasis

variable{B : ι → Submodule R A}(hB : SubmodulesRingBasis B)

theorem to_ring_subgroups_basis (hB : SubmodulesRingBasis B) : RingSubgroupsBasis fun i => (B i).toAddSubgroup :=
  by 
    apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul 
    intro a i 
    rcases hB.left_mul a i with ⟨j, hj⟩
    use j 
    rintro b (b_in : b ∈ B j)
    exact hj ⟨b, b_in, rfl⟩

/-- The topology associated to a basis of submodules in an algebra. -/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.to_ring_subgroups_basis.topology

end SubmodulesRingBasis

variable{M : Type _}[AddCommGroupₓ M][Module R M]

/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesBasis[TopologicalSpace R](B : ι → Submodule R M) : Prop where 
  inter : ∀ i j, ∃ k, B k ≤ B i⊓B j 
  smul : ∀ (m : M) (i : ι), ∀ᶠa in 𝓝 (0 : R), a • m ∈ B i

namespace SubmodulesBasis

variable[TopologicalSpace R][Nonempty ι]{B : ι → Submodule R M}(hB : SubmodulesBasis B)

include hB

/-- The image of a submodules basis is a module filter basis. -/
def to_module_filter_basis : ModuleFilterBasis R M :=
  { Sets := { U | ∃ i, U = B i },
    Nonempty :=
      by 
        inhabit ι 
        exact ⟨B (default ι), default ι, rfl⟩,
    inter_sets :=
      by 
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        cases' hB.inter i j with k hk 
        use B k, k, rfl, hk,
    zero' :=
      by 
        rintro _ ⟨i, rfl⟩
        exact (B i).zero_mem,
    add' :=
      by 
        rintro _ ⟨i, rfl⟩
        use B i, i, rfl 
        rintro x ⟨y, z, y_in, z_in, rfl⟩
        exact (B i).add_mem y_in z_in,
    neg' :=
      by 
        rintro _ ⟨i, rfl⟩
        use B i, i, rfl 
        intro x x_in 
        exact (B i).neg_mem x_in,
    conj' :=
      by 
        rintro x₀ _ ⟨i, rfl⟩
        use B i, i, rfl 
        simp ,
    smul' :=
      by 
        rintro _ ⟨i, rfl⟩
        use univ, univ_mem, B i, i, rfl 
        rintro _ ⟨a, m, -, hm, rfl⟩
        exact (B i).smul_mem _ hm,
    smul_left' :=
      by 
        rintro x₀ _ ⟨i, rfl⟩
        use B i, i, rfl 
        intro m 
        exact (B i).smul_mem _,
    smul_right' :=
      by 
        rintro m₀ _ ⟨i, rfl⟩
        exact hB.smul m₀ i }

/-- The topology associated to a basis of submodules in a module. -/
def topology : TopologicalSpace M :=
  hB.to_module_filter_basis.to_add_group_filter_basis.topology

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/ def open_add_subgroup (i : ι) : @open_add_subgroup M _ hB.topology :=
{ is_open' := begin
    letI [] [] [":=", expr hB.topology],
    rw [expr is_open_iff_mem_nhds] [],
    intros [ident a, ident a_in],
    rw [expr (hB.to_module_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff] [],
    use ["[", expr B i, ",", expr i, ",", expr rfl, "]"],
    rintros ["-", "⟨", ident b, ",", ident b_in, ",", ident rfl, "⟩"],
    exact [expr (B i).add_mem a_in b_in]
  end,
  ..(B i).to_add_subgroup }

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nonarchimedean (hB : submodules_basis B) : @nonarchimedean_add_group M _ hB.topology :=
begin
  letI [] [] [":=", expr hB.topology],
  constructor,
  intros [ident U, ident hU],
  obtain ["⟨", "-", ",", "⟨", ident i, ",", ident rfl, "⟩", ",", ident hi, ":", expr «expr ⊆ »((B i : set M), U), "⟩", ":=", expr hB.to_module_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU],
  exact [expr ⟨hB.open_add_subgroup i, hi⟩]
end

/-- The non archimedean subgroup basis lemmas cannot be instances because some instances
(such as `measure_theory.ae_eq_fun.add_monoid ` or `topological_add_group.to_has_continuous_add`)
cause the search for `@topological_add_group β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/
library_note "nonarchimedean non instances"

end SubmodulesBasis

section 

variable[TopologicalSpace
      R]{B : ι → Submodule R A}(hB : SubmodulesRingBasis B)(hsmul : ∀ (m : A) (i : ι), ∀ᶠa : R in 𝓝 0, a • m ∈ B i)

theorem SubmodulesRingBasis.to_submodules_basis : SubmodulesBasis B :=
  { inter := hB.inter, smul := hsmul }

example  [Nonempty ι] : hB.topology = (hB.to_submodules_basis hsmul).topology :=
  rfl

end 

/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of a `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
structure RingFilterBasis.SubmodulesBasis(BR : RingFilterBasis R)(B : ι → Submodule R M) : Prop where 
  inter : ∀ i j, ∃ k, B k ≤ B i⊓B j 
  smul : ∀ (m : M) (i : ι), ∃ (U : _)(_ : U ∈ BR), U ⊆ (fun a => a • m) ⁻¹' B i

-- error in Topology.Algebra.Nonarchimedean.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_filter_basis.submodules_basis_is_basis
(BR : ring_filter_basis R)
{B : ι → submodule R M}
(hB : BR.submodules_basis B) : @submodules_basis ι R _ M _ _ BR.topology B :=
{ inter := hB.inter,
  smul := begin
    letI [] [] [":=", expr BR.topology],
    intros [ident m, ident i],
    rcases [expr hB.smul m i, "with", "⟨", ident V, ",", ident V_in, ",", ident hV, "⟩"],
    exact [expr mem_of_superset (BR.to_add_group_filter_basis.mem_nhds_zero V_in) hV]
  end }

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
  (hB : BR.submodules_basis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodules_basis_is_basis hB)

