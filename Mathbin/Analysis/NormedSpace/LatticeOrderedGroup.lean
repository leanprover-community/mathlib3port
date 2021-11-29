import Mathbin.Topology.Order.Lattice 
import Mathbin.Analysis.Normed.Group.Basic 
import Mathbin.Algebra.LatticeOrderedGroup

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/


/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/


local notation "|" a "|" => abs a

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `∥a∥ ≤ ∥b∥`. Then `α` is
said to be a normed lattice ordered group.
-/
class NormedLatticeAddCommGroup(α : Type _) extends NormedGroup α, Lattice α where 
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), (c+a) ≤ c+b 
  solid : ∀ (a b : α), |a| ≤ |b| → ∥a∥ ≤ ∥b∥

theorem solid {α : Type _} [NormedLatticeAddCommGroup α] {a b : α} (h : |a| ≤ |b|) : ∥a∥ ≤ ∥b∥ :=
  NormedLatticeAddCommGroup.solid a b h

/--
A normed lattice ordered group is an ordered additive commutative group
-/
instance (priority := 100)normedLatticeAddCommGroupToOrderedAddCommGroup {α : Type _}
  [h : NormedLatticeAddCommGroup α] : OrderedAddCommGroup α :=
  { h with  }

/--
Let `α` be a normed group with a partial order. Then the order dual is also a normed group.
-/
instance (priority := 100) {α : Type _} : ∀ [NormedGroup α], NormedGroup (OrderDual α) :=
  id

/--
Let `α` be a normed lattice ordered group and let `a` and `b` be elements of `α`. Then `a⊓-a ≥ b⊓-b`
implies `∥a∥ ≤ ∥b∥`.
-/
theorem dual_solid {α : Type _} [NormedLatticeAddCommGroup α] (a b : α) (h : b⊓-b ≤ a⊓-a) : ∥a∥ ≤ ∥b∥ :=
  by 
    apply solid 
    rw [abs_eq_sup_neg]
    nthRw 0[←neg_negₓ a]
    rw [←neg_inf_eq_sup_neg]
    rw [abs_eq_sup_neg]
    nthRw 0[←neg_negₓ b]
    rw [←neg_inf_eq_sup_neg]
    finish

/--
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) {α : Type _} [h : NormedLatticeAddCommGroup α] : NormedLatticeAddCommGroup (OrderDual α) :=
  { add_le_add_left :=
      by 
        intro a b h₁ c 
        rw [←OrderDual.dual_le]
        rw [←OrderDual.dual_le] at h₁ 
        apply h.add_le_add_left 
        exact h₁,
    solid :=
      by 
        intro a b h₂ 
        apply dual_solid 
        rw [←OrderDual.dual_le] at h₂ 
        finish }

/--
Let `α` be a normed lattice ordered group, let `a` be an element of `α` and let `|a|` be the
absolute value of `a`. Then `∥|a|∥ = ∥a∥`.
-/
theorem norm_abs_eq_norm {α : Type _} [NormedLatticeAddCommGroup α] (a : α) : ∥|a|∥ = ∥a∥ :=
  by 
    rw [le_antisymm_iffₓ]
    split 
    ·
      apply NormedLatticeAddCommGroup.solid 
      rw [←LatticeOrderedCommGroup.abs_idempotent a]
    ·
      apply NormedLatticeAddCommGroup.solid 
      rw [←LatticeOrderedCommGroup.abs_idempotent a]

-- error in Analysis.NormedSpace.LatticeOrderedGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
@[priority 100]
instance normed_lattice_add_comm_group_has_continuous_inf
{α : Type*}
[normed_lattice_add_comm_group α] : has_continuous_inf α :=
⟨«expr $ »(continuous_iff_continuous_at.2, λ
  q, «expr $ »(tendsto_iff_norm_tendsto_zero.2, begin
     have [] [":", expr ∀
      p : «expr × »(α, α), «expr ≤ »(«expr∥ ∥»(«expr - »(«expr ⊓ »(p.1, p.2), «expr ⊓ »(q.1, q.2))), «expr + »(«expr∥ ∥»(«expr - »(p.1, q.1)), «expr∥ ∥»(«expr - »(p.2, q.2))))] [],
     { intros [],
       nth_rewrite_rhs [0] ["<-", expr norm_abs_eq_norm] [],
       nth_rewrite_rhs [1] ["<-", expr norm_abs_eq_norm] [],
       apply [expr le_trans _ (norm_add_le «expr| |»(«expr - »(p.fst, q.fst)) «expr| |»(«expr - »(p.snd, q.snd)))],
       apply [expr normed_lattice_add_comm_group.solid],
       rw [expr lattice_ordered_comm_group.abs_pos_eq «expr + »(«expr| |»(«expr - »(p.fst, q.fst)), «expr| |»(«expr - »(p.snd, q.snd)))] [],
       { calc
           «expr = »(«expr| |»(«expr - »(«expr ⊓ »(p.fst, p.snd), «expr ⊓ »(q.fst, q.snd))), «expr| |»(«expr + »(«expr - »(«expr ⊓ »(p.fst, p.snd), «expr ⊓ »(q.fst, p.snd)), «expr - »(«expr ⊓ »(q.fst, p.snd), «expr ⊓ »(q.fst, q.snd))))) : by { rw [expr sub_add_sub_cancel] [] }
           «expr ≤ »(..., «expr + »(«expr| |»(«expr - »(«expr ⊓ »(p.fst, p.snd), «expr ⊓ »(q.fst, p.snd))), «expr| |»(«expr - »(«expr ⊓ »(q.fst, p.snd), «expr ⊓ »(q.fst, q.snd))))) : by { apply [expr lattice_ordered_comm_group.abs_triangle] }
           «expr ≤ »(..., «expr + »(«expr| |»(«expr - »(p.fst, q.fst)), «expr| |»(«expr - »(p.snd, q.snd)))) : by { apply [expr add_le_add],
             { exact [expr (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right] },
             { rw [expr inf_comm] [],
               nth_rewrite [1] [expr inf_comm] [],
               exact [expr (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right] } } },
       { exact [expr add_nonneg (lattice_ordered_comm_group.abs_pos «expr - »(p.fst, q.fst)) (lattice_ordered_comm_group.abs_pos «expr - »(p.snd, q.snd))] } },
     refine [expr squeeze_zero (λ e, norm_nonneg _) this _],
     convert [] [expr ((continuous_fst.tendsto q).sub tendsto_const_nhds).norm.add ((continuous_snd.tendsto q).sub tendsto_const_nhds).norm] [],
     simp [] [] [] [] [] []
   end))⟩

/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
instance (priority := 100)normedLatticeAddCommGroupTopologicalLattice {α : Type _} [NormedLatticeAddCommGroup α] :
  TopologicalLattice α :=
  TopologicalLattice.mk

