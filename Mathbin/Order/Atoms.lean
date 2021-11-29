import Mathbin.Order.CompleteBooleanAlgebra 
import Mathbin.Order.ModularLattice 
import Mathbin.Data.Fintype.Basic

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_lattice` indicates that a bounded lattice has only two elements, `⊥` and `⊤`.
  * `is_simple_lattice.bounded_order`
  * `is_simple_lattice.distrib_lattice`
  * Given an instance of `is_simple_lattice`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_lattice.boolean_algebra`
    * `is_simple_lattice.complete_lattice`
    * `is_simple_lattice.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_lattice_iff_is_atom_top` and `is_simple_lattice_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * ``is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/


variable{α : Type _}

section Atoms

section IsAtom

variable[PartialOrderₓ α][OrderBot α]

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥

theorem eq_bot_or_eq_of_le_atom {a b : α} (ha : IsAtom a) (hab : b ≤ a) : b = ⊥ ∨ b = a :=
  hab.lt_or_eq.imp_left (ha.2 b)

theorem IsAtom.Iic {x a : α} (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, hb⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsAtom.of_is_atom_coe_Iic {x : α} {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba => Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

end IsAtom

section IsCoatom

variable[PartialOrderₓ α][OrderTop α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤

theorem eq_top_or_eq_of_coatom_le {a b : α} (ha : IsCoatom a) (hab : a ≤ b) : b = ⊤ ∨ b = a :=
  hab.lt_or_eq.imp (ha.2 b) eq_comm.2

theorem IsCoatom.Ici {x a : α} (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, hb⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsCoatom.of_is_coatom_coe_Ici {x : α} {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba => Subtype.mk_eq_mk.1 (ha.2 ⟨b, le_transₓ a.prop hba.le⟩ hba)⟩

end IsCoatom

section Pairwise

theorem IsAtom.inf_eq_bot_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a) (hb : IsAtom b)
  (hab : a ≠ b) : a⊓b = ⊥ :=
  Or.elim (eq_bot_or_eq_of_le_atom ha inf_le_left) id
    fun h1 =>
      Or.elim (eq_bot_or_eq_of_le_atom hb inf_le_right) id
        fun h2 => False.ndrec _ (hab (le_antisymmₓ (inf_eq_left.mp h1) (inf_eq_right.mp h2)))

theorem IsAtom.disjoint_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
  Disjoint a b :=
  disjoint_iff.mpr (IsAtom.inf_eq_bot_of_ne ha hb hab)

theorem IsCoatom.sup_eq_top_of_ne [SemilatticeSup α] [OrderTop α] {a b : α} (ha : IsCoatom a) (hb : IsCoatom b)
  (hab : a ≠ b) : a⊔b = ⊤ :=
  Or.elim (eq_top_or_eq_of_coatom_le ha le_sup_left) id
    fun h1 =>
      Or.elim (eq_top_or_eq_of_coatom_le hb le_sup_right) id
        fun h2 => False.ndrec _ (hab (le_antisymmₓ (sup_eq_right.mp h2) (sup_eq_left.mp h1)))

end Pairwise

variable[PartialOrderₓ α]{a : α}

@[simp]
theorem is_coatom_dual_iff_is_atom [OrderBot α] : IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
theorem is_atom_dual_iff_is_coatom [OrderTop α] : IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

end Atoms

section Atomic

variable[PartialOrderₓ α](α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
class IsAtomic[OrderBot α] : Prop where 
  eq_bot_or_exists_atom_le : ∀ (b : α), b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
class IsCoatomic[OrderTop α] : Prop where 
  eq_top_or_exists_le_coatom : ∀ (b : α), b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a

export IsAtomic(eq_bot_or_exists_atom_le)

export IsCoatomic(eq_top_or_exists_le_coatom)

variable{α}

@[simp]
theorem is_coatomic_dual_iff_is_atomic [OrderBot α] : IsCoatomic (OrderDual α) ↔ IsAtomic α :=
  ⟨fun h =>
      ⟨fun b =>
          by 
            apply h.eq_top_or_exists_le_coatom⟩,
    fun h =>
      ⟨fun b =>
          by 
            apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]
theorem is_atomic_dual_iff_is_coatomic [OrderTop α] : IsAtomic (OrderDual α) ↔ IsCoatomic α :=
  ⟨fun h =>
      ⟨fun b =>
          by 
            apply h.eq_bot_or_exists_atom_le⟩,
    fun h =>
      ⟨fun b =>
          by 
            apply h.eq_top_or_exists_le_coatom⟩⟩

namespace IsAtomic

variable[OrderBot α][IsAtomic α]

instance is_coatomic_dual : IsCoatomic (OrderDual α) :=
  is_coatomic_dual_iff_is_atomic.2 ‹IsAtomic α›

instance  {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
      (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2
        fun ⟨a, ha, hay⟩ => ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable[OrderTop α][IsCoatomic α]

instance IsCoatomic : IsAtomic (OrderDual α) :=
  is_atomic_dual_iff_is_coatomic.2 ‹IsCoatomic α›

instance  {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
      (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2
        fun ⟨a, ha, hay⟩ => ⟨⟨a, le_transₓ hy hay⟩, ha.Ici (le_transₓ hy hay), hay⟩⟩

end IsCoatomic

theorem is_atomic_iff_forall_is_atomic_Iic [OrderBot α] : IsAtomic α ↔ ∀ (x : α), IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.is_atomic _ _ _,
    fun h =>
      ⟨fun x =>
          ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
            (exists_imp_exists' coeₓ fun ⟨a, ha⟩ => And.imp_left IsAtom.of_is_atom_coe_Iic)⟩⟩

theorem is_coatomic_iff_forall_is_coatomic_Ici [OrderTop α] : IsCoatomic α ↔ ∀ (x : α), IsCoatomic (Set.Ici x) :=
  is_atomic_dual_iff_is_coatomic.symm.trans$
    is_atomic_iff_forall_is_atomic_Iic.trans$ forall_congrₓ fun x => is_coatomic_dual_iff_is_atomic.symm.trans Iff.rfl

end Atomic

section Atomistic

variable(α)[CompleteLattice α]

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class IsAtomistic : Prop where 
  eq_Sup_atoms : ∀ (b : α), ∃ s : Set α, b = Sup s ∧ ∀ a, a ∈ s → IsAtom a

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class IsCoatomistic : Prop where 
  eq_Inf_coatoms : ∀ (b : α), ∃ s : Set α, b = Inf s ∧ ∀ a, a ∈ s → IsCoatom a

export IsAtomistic(eq_Sup_atoms)

export IsCoatomistic(eq_Inf_coatoms)

variable{α}

@[simp]
theorem is_coatomistic_dual_iff_is_atomistic : IsCoatomistic (OrderDual α) ↔ IsAtomistic α :=
  ⟨fun h =>
      ⟨fun b =>
          by 
            apply h.eq_Inf_coatoms⟩,
    fun h =>
      ⟨fun b =>
          by 
            apply h.eq_Sup_atoms⟩⟩

@[simp]
theorem is_atomistic_dual_iff_is_coatomistic : IsAtomistic (OrderDual α) ↔ IsCoatomistic α :=
  ⟨fun h =>
      ⟨fun b =>
          by 
            apply h.eq_Sup_atoms⟩,
    fun h =>
      ⟨fun b =>
          by 
            apply h.eq_Inf_coatoms⟩⟩

namespace IsAtomistic

instance is_coatomistic_dual [h : IsAtomistic α] : IsCoatomistic (OrderDual α) :=
  is_coatomistic_dual_iff_is_atomistic.2 h

variable[IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b =>
      by 
        rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
        cases' s.eq_empty_or_nonempty with h h
        ·
          simp [h]
        ·
          exact Or.intro_rightₓ _ ⟨h.some, hs _ h.some_spec, le_Sup h.some_spec⟩⟩

end IsAtomistic

section IsAtomistic

variable[IsAtomistic α]

@[simp]
theorem Sup_atoms_le_eq (b : α) : Sup { a:α | IsAtom a ∧ a ≤ b } = b :=
  by 
    rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
    exact le_antisymmₓ (Sup_le fun _ => And.right) (Sup_le_Sup fun a ha => ⟨hs a ha, le_Sup ha⟩)

@[simp]
theorem Sup_atoms_eq_top : Sup { a:α | IsAtom a } = ⊤ :=
  by 
    refine' Eq.trans (congr rfl (Set.ext fun x => _)) (Sup_atoms_le_eq ⊤)
    exact (and_iff_left le_top).symm

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ (c : α), IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_transₓ ca ab,
    fun h =>
      by 
        rw [←Sup_atoms_le_eq a, ←Sup_atoms_le_eq b]
        exact Sup_le_Sup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

end IsAtomistic

namespace IsCoatomistic

instance is_atomistic_dual [h : IsCoatomistic α] : IsAtomistic (OrderDual α) :=
  is_atomistic_dual_iff_is_coatomistic.2 h

variable[IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b =>
      by 
        rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩
        cases' s.eq_empty_or_nonempty with h h
        ·
          simp [h]
        ·
          exact Or.intro_rightₓ _ ⟨h.some, hs _ h.some_spec, Inf_le h.some_spec⟩⟩

end IsCoatomistic

end Atomistic

/-- A lattice is simple iff it has only two elements, `⊥` and `⊤`. -/
class IsSimpleLattice(α : Type _)[Lattice α][BoundedOrder α] extends Nontrivial α : Prop where 
  eq_bot_or_eq_top : ∀ (a : α), a = ⊥ ∨ a = ⊤

export IsSimpleLattice(eq_bot_or_eq_top)

-- error in Order.Atoms: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_simple_lattice_iff_is_simple_lattice_order_dual
[lattice α]
[bounded_order α] : «expr ↔ »(is_simple_lattice α, is_simple_lattice (order_dual α)) :=
begin
  split; intro [ident i]; haveI [] [] [":=", expr i],
  { exact [expr { exists_pair_ne := @exists_pair_ne α _,
       eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top (order_dual.of_dual a) : «expr ∨ »(_, _)) }] },
  { exact [expr { exists_pair_ne := @exists_pair_ne (order_dual α) _,
       eq_bot_or_eq_top := λ a, or.symm (eq_bot_or_eq_top (order_dual.to_dual a)) }] }
end

section IsSimpleLattice

variable[Lattice α][BoundedOrder α][IsSimpleLattice α]

instance  : IsSimpleLattice (OrderDual α) :=
  is_simple_lattice_iff_is_simple_lattice_order_dual.1
    (by 
      infer_instance)

@[simp]
theorem is_atom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_ltₓ ha)⟩

@[simp]
theorem is_coatom_bot : IsCoatom (⊥ : α) :=
  is_atom_dual_iff_is_coatom.1 is_atom_top

end IsSimpleLattice

namespace IsSimpleLattice

section BoundedOrder

variable[Lattice α][BoundedOrder α][IsSimpleLattice α]

/-- A simple `bounded_order` is also distributive. -/
instance (priority := 100) : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf :=
      fun x y z =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp  }

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨is_atom_top, ge_of_eq h⟩⟩⟩

instance (priority := 100) : IsCoatomic α :=
  is_atomic_dual_iff_is_coatomic.1 IsSimpleLattice.is_atomic

end BoundedOrder

section DecidableEq

variable[DecidableEq α][Lattice α][BoundedOrder α][IsSimpleLattice α]

/-- Every simple lattice is order-isomorphic to `bool`. -/
def order_iso_bool : α ≃o Bool :=
  { toFun := fun x => x = ⊤, invFun := fun x => cond x ⊤ ⊥,
    left_inv :=
      fun x =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top],
    right_inv :=
      fun x =>
        by 
          cases x <;> simp [bot_ne_top],
    map_rel_iff' :=
      fun a b =>
        by 
          rcases eq_bot_or_eq_top a with (rfl | rfl)
          ·
            simp [bot_ne_top]
          ·
            rcases eq_bot_or_eq_top b with (rfl | rfl)
            ·
              simp [bot_ne_top.symm, bot_ne_top, Bool.ff_lt_tt]
            ·
              simp [bot_ne_top] }

instance (priority := 200) : Fintype α :=
  Fintype.ofEquiv Bool order_iso_bool.toEquiv.symm

/-- A simple `bounded_order` is also a `boolean_algebra`. -/
protected def BooleanAlgebra : BooleanAlgebra α :=
  { show BoundedOrder α by 
      infer_instance,
    IsSimpleLattice.distribLattice with Compl := fun x => if x = ⊥ then ⊤ else ⊥,
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥,
    sdiff_eq :=
      fun x y =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top, HasSdiff.sdiff, compl],
    inf_compl_le_bot :=
      fun x =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            simp 
          ·
            simp only [top_inf_eq]
            splitIfs with h h <;> simp [h],
    top_le_sup_compl :=
      fun x =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp ,
    sup_inf_sdiff :=
      fun x y =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl) <;>
            rcases eq_bot_or_eq_top y with (rfl | rfl) <;> simp [bot_ne_top],
    inf_inf_sdiff :=
      fun x y =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            simpa 
          rcases eq_bot_or_eq_top y with (rfl | rfl)
          ·
            simpa
          ·
            simp only [true_andₓ, top_inf_eq, eq_self_iff_true]
            splitIfs with h h <;> simpa [h] }

end DecidableEq

variable[Lattice α][BoundedOrder α][IsSimpleLattice α]

open_locale Classical

/-- A simple `bounded_order` is also complete. -/
protected noncomputable def CompleteLattice : CompleteLattice α :=
  { (inferInstance : Lattice α), (inferInstance : BoundedOrder α) with sup := fun s => if ⊤ ∈ s then ⊤ else ⊥,
    inf := fun s => if ⊥ ∈ s then ⊥ else ⊤,
    le_Sup :=
      fun s x h =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            exact bot_le
          ·
            rw [if_pos h],
    Sup_le :=
      fun s x h =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            rw [if_neg]
            intro con 
            exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
          ·
            exact le_top,
    Inf_le :=
      fun s x h =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            rw [if_pos h]
          ·
            exact le_top,
    le_Inf :=
      fun s x h =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            exact bot_le
          ·
            rw [if_neg]
            intro con 
            exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }

/-- A simple `bounded_order` is also a `complete_boolean_algebra`. -/
protected noncomputable def CompleteBooleanAlgebra : CompleteBooleanAlgebra α :=
  { IsSimpleLattice.completeLattice, IsSimpleLattice.booleanAlgebra with
    infi_sup_le_sup_Inf :=
      fun x s =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            simp only [bot_sup_eq, ←Inf_eq_infi]
            apply le_reflₓ
          ·
            simp only [top_sup_eq, le_top],
    inf_Sup_le_supr_inf :=
      fun x s =>
        by 
          rcases eq_bot_or_eq_top x with (rfl | rfl)
          ·
            simp only [bot_inf_eq, bot_le]
          ·
            simp only [top_inf_eq, ←Sup_eq_supr]
            apply le_reflₓ }

end IsSimpleLattice

namespace IsSimpleLattice

variable[CompleteLattice α][IsSimpleLattice α]

set_option default_priority 100

instance  : IsAtomistic α :=
  ⟨fun b =>
      (eq_bot_or_eq_top b).elim
        (fun h => ⟨∅, ⟨h.trans Sup_empty.symm, fun a ha => False.elim (Set.not_mem_empty _ ha)⟩⟩)
        fun h => ⟨{⊤}, h.trans Sup_singleton.symm, fun a ha => (Set.mem_singleton_iff.1 ha).symm ▸ is_atom_top⟩⟩

instance  : IsCoatomistic α :=
  is_atomistic_dual_iff_is_coatomistic.1 IsSimpleLattice.is_atomistic

end IsSimpleLattice

namespace Fintype

namespace IsSimpleLattice

variable[Lattice α][BoundedOrder α][IsSimpleLattice α][DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} :=
  by 
    change Finset.map _ (Finset.univ : Finset Bool) = _ 
    rw [Fintype.univ_bool]
    simp only [Finset.map_insert, Function.Embedding.coe_fn_mk, Finset.map_singleton]
    rfl

theorem card : Fintype.card α = 2 :=
  (Fintype.of_equiv_card _).trans Fintype.card_bool

end IsSimpleLattice

end Fintype

namespace Bool

instance  : IsSimpleLattice Bool :=
  ⟨fun a =>
      by 
        rw [←Finset.mem_singleton, Or.comm, ←Finset.mem_insert, top_eq_tt, bot_eq_ff, ←Fintype.univ_bool]
        apply Finset.mem_univ⟩

end Bool

theorem is_simple_lattice_iff_is_atom_top [Lattice α] [BoundedOrder α] : IsSimpleLattice α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @is_atom_top _ _ _ h,
    fun h =>
      { exists_pair_ne := ⟨⊤, ⊥, h.1⟩, eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

theorem is_simple_lattice_iff_is_coatom_bot [Lattice α] [BoundedOrder α] : IsSimpleLattice α ↔ IsCoatom (⊥ : α) :=
  is_simple_lattice_iff_is_simple_lattice_order_dual.trans is_simple_lattice_iff_is_atom_top

namespace Set

theorem is_simple_lattice_Iic_iff_is_atom [Lattice α] [BoundedOrder α] {a : α} : IsSimpleLattice (Iic a) ↔ IsAtom a :=
  is_simple_lattice_iff_is_atom_top.trans$
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_ltₓ ab⟩ ab),
        fun h ⟨b, hab⟩ hbotb => Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

theorem is_simple_lattice_Ici_iff_is_coatom [Lattice α] [BoundedOrder α] {a : α} :
  IsSimpleLattice (Ici a) ↔ IsCoatom a :=
  is_simple_lattice_iff_is_coatom_bot.trans$
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_ltₓ ab⟩ ab),
        fun h ⟨b, hab⟩ hbotb => Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

end Set

namespace OrderIso

variable{β : Type _}

@[simp]
theorem is_atom_iff [PartialOrderₓ α] [OrderBot α] [PartialOrderₓ β] [OrderBot β] (f : α ≃o β) (a : α) :
  IsAtom (f a) ↔ IsAtom a :=
  and_congr (not_congr ⟨fun h => f.injective (f.map_bot.symm ▸ h), fun h => f.map_bot ▸ congr rfl h⟩)
    ⟨fun h b hb => f.injective ((h (f b) ((f : α ↪o β).lt_iff_lt.2 hb)).trans f.map_bot.symm),
      fun h b hb =>
        f.symm.injective
          (by 
            rw [f.symm.map_bot]
            apply h 
            rw [←f.symm_apply_apply a]
            exact (f.symm : β ↪o α).lt_iff_lt.2 hb)⟩

@[simp]
theorem is_coatom_iff [PartialOrderₓ α] [OrderTop α] [PartialOrderₓ β] [OrderTop β] (f : α ≃o β) (a : α) :
  IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.is_atom_iff a

theorem is_simple_lattice_iff [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] (f : α ≃o β) :
  IsSimpleLattice α ↔ IsSimpleLattice β :=
  by 
    rw [is_simple_lattice_iff_is_atom_top, is_simple_lattice_iff_is_atom_top, ←f.is_atom_iff ⊤, f.map_top]

theorem IsSimpleLattice [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [h : IsSimpleLattice β] (f : α ≃o β) :
  IsSimpleLattice α :=
  f.is_simple_lattice_iff.mpr h

theorem is_atomic_iff [PartialOrderₓ α] [OrderBot α] [PartialOrderₓ β] [OrderBot β] (f : α ≃o β) :
  IsAtomic α ↔ IsAtomic β :=
  by 
    suffices  : (∀ (b : α), b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b) ↔ ∀ (b : β), b = ⊥ ∨ ∃ a : β, IsAtom a ∧ a ≤ b 
    exact ⟨fun ⟨p⟩ => ⟨this.mp p⟩, fun ⟨p⟩ => ⟨this.mpr p⟩⟩
    apply f.to_equiv.forall_congr 
    simpRw [RelIso.coe_fn_to_equiv]
    intro b 
    apply or_congr
    ·
      rw [f.apply_eq_iff_eq_symm_apply, map_bot]
    ·
      split 
      ·
        exact fun ⟨a, ha⟩ => ⟨f a, ⟨(f.is_atom_iff a).mpr ha.1, f.le_iff_le.mpr ha.2⟩⟩
      ·
        rintro ⟨b, ⟨hb1, hb2⟩⟩
        refine' ⟨f.symm b, ⟨(f.symm.is_atom_iff b).mpr hb1, _⟩⟩
        rwa [←f.le_iff_le, f.apply_symm_apply]

theorem is_coatomic_iff [PartialOrderₓ α] [OrderTop α] [PartialOrderₓ β] [OrderTop β] (f : α ≃o β) :
  IsCoatomic α ↔ IsCoatomic β :=
  by 
    rw [←is_atomic_dual_iff_is_coatomic, ←is_atomic_dual_iff_is_coatomic]
    exact f.dual.is_atomic_iff

end OrderIso

section IsModularLattice

variable[Lattice α][BoundedOrder α][IsModularLattice α]

namespace IsCompl

variable{a b : α}(hc : IsCompl a b)

include hc

theorem is_atom_iff_is_coatom : IsAtom a ↔ IsCoatom b :=
  Set.is_simple_lattice_Iic_iff_is_atom.symm.trans$
    hc.Iic_order_iso_Ici.is_simple_lattice_iff.trans Set.is_simple_lattice_Ici_iff_is_coatom

theorem is_coatom_iff_is_atom : IsCoatom a ↔ IsAtom b :=
  hc.symm.is_atom_iff_is_coatom.symm

end IsCompl

variable[IsComplemented α]

theorem is_coatomic_of_is_atomic_of_is_complemented_of_is_modular [IsAtomic α] : IsCoatomic α :=
  ⟨fun x =>
      by 
        rcases exists_is_compl x with ⟨y, xy⟩
        apply (eq_bot_or_exists_atom_le y).imp _ _
        ·
          rintro rfl 
          exact eq_top_of_is_compl_bot xy
        ·
          rintro ⟨a, ha, ay⟩
          rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
          refine' ⟨«expr↑ » (⟨b, xb⟩ : Set.Ici x), IsCoatom.of_is_coatom_coe_Ici _, xb⟩
          rw [←hb.is_atom_iff_is_coatom, OrderIso.is_atom_iff]
          apply ha.Iic⟩

theorem is_atomic_of_is_coatomic_of_is_complemented_of_is_modular [IsCoatomic α] : IsAtomic α :=
  is_coatomic_dual_iff_is_atomic.1 is_coatomic_of_is_atomic_of_is_complemented_of_is_modular

theorem is_atomic_iff_is_coatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @is_coatomic_of_is_atomic_of_is_complemented_of_is_modular _ _ _ _ _ h,
    fun h => @is_atomic_of_is_coatomic_of_is_complemented_of_is_modular _ _ _ _ _ h⟩

end IsModularLattice

