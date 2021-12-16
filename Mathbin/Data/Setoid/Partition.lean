import Mathbin.Data.Fintype.Basic 
import Mathbin.Data.Set.Finite 
import Mathbin.Data.Setoid.Basic

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : set (set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `is_partition c`
* An indexed partition is a map `s : ι → α` whose image is a partition. This is
  expressed as `indexed_partition s`.

Of course both implementations are related to `quotient` and `setoid`.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/


namespace Setoidₓ

variable {α : Type _}

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {x b b'} (hc : b ∈ c) (hb : x ∈ b)
  (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  (H x).unique2 hc hb hc' hb'

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » c)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mk_classes (c : Set (Set α)) (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) : Setoidₓ α :=
  ⟨fun x y => ∀ s _ : s ∈ c, x ∈ s → y ∈ s,
    ⟨fun _ _ _ hx => hx,
      fun x y h s hs hy =>
        (H x).elim2$
          fun t ht hx _ =>
            have  : s = t := eq_of_mem_eqv_class H hs hy ht (h t ht hx)
            this.symm ▸ hx,
      fun x y z h1 h2 s hs hx =>
        (H y).elim2$
          fun t ht hy _ =>
            (H z).elim2$
              fun t' ht' hz _ =>
                have hst : s = t := eq_of_mem_eqv_class H hs (h1 _ hs hx) ht hy 
                have htt' : t = t' := eq_of_mem_eqv_class H ht (h2 _ ht hy) ht' hz
                (hst.trans htt').symm ▸ hz⟩⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- Makes the equivalence classes of an equivalence relation. -/
  def classes ( r : Setoidₓ α ) : Set Set α := { s | ∃ y , s = { x | r.rel x y } }

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem mem_classes ( r : Setoidₓ α ) y : { x | r.rel x y } ∈ r.classes := ⟨ y , rfl ⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  classes_ker_subset_fiber_set
  { β : Type _ } ( f : α → β ) : Setoidₓ.ker f . Classes ⊆ Set.Range fun y => { x | f x = y }
  := by rintro s ⟨ x , rfl ⟩ rw [ Set.mem_range ] exact ⟨ f x , rfl ⟩

theorem nonempty_fintype_classes_ker {α β : Type _} [Fintype β] (f : α → β) :
  Nonempty (Fintype (Setoidₓ.ker f).Classes) :=
  by 
    classical 
    exact ⟨Set.fintypeSubset _ (classes_ker_subset_fiber_set f)⟩

theorem card_classes_ker_le {α β : Type _} [Fintype β] (f : α → β) [Fintype (Setoidₓ.ker f).Classes] :
  Fintype.card (Setoidₓ.ker f).Classes ≤ Fintype.card β :=
  by 
    classical 
    exact le_transₓ (Set.card_le_of_subset (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
  theorem
    eq_iff_classes_eq
    { r₁ r₂ : Setoidₓ α } : r₁ = r₂ ↔ ∀ x , { y | r₁.rel x y } = { y | r₂.rel x y }
    := ⟨ fun h x => h ▸ rfl , fun h => ext' $ fun x => Set.ext_iff . 1 $ h x ⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » r.classes)
theorem rel_iff_exists_classes (r : Setoidₓ α) {x y} : r.rel x y ↔ ∃ (c : _)(_ : c ∈ r.classes), x ∈ c ∧ y ∈ c :=
  ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩,
    fun ⟨c, ⟨z, hz⟩, hx, hy⟩ =>
      by 
        subst c 
        exact r.trans' hx (r.symm' hy)⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
theorem classes_inj {r₁ r₂ : Setoidₓ α} : r₁ = r₂ ↔ r₁.classes = r₂.classes :=
  ⟨fun h => h ▸ rfl,
    fun h =>
      ext'$
        fun a b =>
          by 
            simp only [rel_iff_exists_classes, exists_prop, h]⟩

/-- The empty set is not an equivalence class. -/
theorem empty_not_mem_classes {r : Setoidₓ α} : ∅ ∉ r.classes :=
  fun ⟨y, hy⟩ => Set.not_mem_empty y$ hy.symm ▸ r.refl' y

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » r.classes)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- Equivalence classes partition the type. -/
  theorem
    classes_eqv_classes
    { r : Setoidₓ α } a : ∃! ( b : _ ) ( _ : b ∈ r.classes ) , a ∈ b
    :=
      ExistsUnique.intro2 { x | r.rel x a } r.mem_classes a r.refl' _
        $
        by rintro _ ⟨ y , rfl ⟩ ha ext x exact ⟨ fun hx => r.trans' hx r.symm' ha , fun hx => r.trans' hx ha ⟩

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
theorem eq_of_mem_classes {r : Setoidₓ α} {x b} (hc : b ∈ r.classes) (hb : x ∈ b) {b'} (hc' : b' ∈ r.classes)
  (hb' : x ∈ b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    The elements of a set of sets partitioning α are the equivalence classes of the
        equivalence relation defined by the set of sets. -/
  theorem
    eq_eqv_class_of_mem
    { c : Set Set α } ( H : ∀ a , ∃! ( b : _ ) ( _ : b ∈ c ) , a ∈ b ) { s y } ( hs : s ∈ c ) ( hy : y ∈ s )
      : s = { x | mk_classes c H . Rel x y }
    :=
      Set.ext
        $
        fun
          x
            =>
            ⟨
              fun hs' => symm' mk_classes c H $ fun b' hb' h' => eq_of_mem_eqv_class H hs hy hb' h' ▸ hs'
                ,
                fun
                  hx => H x . elim2 $ fun b' hc' hb' h' => eq_of_mem_eqv_class H hs hy hc' $ hx b' hc' hb' . symm ▸ hb'
              ⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    The equivalence classes of the equivalence relation defined by a set of sets
        partitioning α are elements of the set of sets. -/
  theorem
    eqv_class_mem
    { c : Set Set α } ( H : ∀ a , ∃! ( b : _ ) ( _ : b ∈ c ) , a ∈ b ) { y } : { x | mk_classes c H . Rel x y } ∈ c
    := H y . elim2 $ fun b hc hy hb => eq_eqv_class_of_mem H hc hy ▸ hc

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
theorem eqv_class_mem' {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) {x} :
  { y : α | (mk_classes c H).Rel x y } ∈ c :=
  by 
    convert Setoidₓ.eqv_class_mem H 
    ext 
    rw [Setoidₓ.comm']

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
/-- Distinct elements of a set of sets partitioning α are disjoint. -/
theorem eqv_classes_disjoint {c : Set (Set α)} (H : ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b) : c.pairwise_disjoint id :=
  fun b₁ h₁ b₂ h₂ h =>
    Set.disjoint_left.2$ fun x hx1 hx2 => (H x).elim2$ fun b hc hx hb => h$ eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
/-- A set of disjoint sets covering α partition α (classical). -/
theorem eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.SUnion c = @Set.Univ α) (H : c.pairwise_disjoint id)
  a : ∃! (b : _)(_ : b ∈ c), a ∈ b :=
  let ⟨b, hc, ha⟩ :=
    Set.mem_sUnion.1$
      show a ∈ _ by 
        rw [hu] <;> exact Set.mem_univ a 
  ExistsUnique.intro2 b hc ha$ fun b' hc' ha' => H.elim_set hc' hc a ha' ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {c : Set (Set α)} (hu : Set.SUnion c = @Set.Univ α) (H : c.pairwise_disjoint id) :
  Setoidₓ α :=
  Setoidₓ.mkClasses c$ eqv_classes_of_disjoint_union hu H

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    The equivalence relation made from the equivalence classes of an equivalence
        relation r equals r. -/
  theorem
    mk_classes_classes
    ( r : Setoidₓ α ) : mk_classes r.classes classes_eqv_classes = r
    :=
      ext'
        $
        fun
          x y
            =>
            ⟨
              fun h => r.symm' h { z | r.rel z x } r.mem_classes x $ r.refl' x
                ,
                fun h b hb hx => eq_of_mem_classes r.mem_classes x r.refl' x hb hx ▸ r.symm' h
              ⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    sUnion_classes
    ( r : Setoidₓ α ) : ⋃₀ r.classes = Set.Univ
    := Set.eq_univ_of_forall $ fun x => Set.mem_sUnion . 2 ⟨ { y | r.rel y x } , ⟨ x , rfl ⟩ , Setoidₓ.refl _ ⟩

section Partition

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » c)
/-- A collection `c : set (set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def is_partition (c : Set (Set α)) :=
  ∅ ∉ c ∧ ∀ a, ∃! (b : _)(_ : b ∈ c), a ∈ b

/-- A partition of `α` does not contain the empty set. -/
theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : is_partition c) {s} (h : s ∈ c) : s.nonempty :=
  Set.ne_empty_iff_nonempty.1$ fun hs0 => hc.1$ hs0 ▸ h

theorem is_partition_classes (r : Setoidₓ α) : is_partition r.classes :=
  ⟨empty_not_mem_classes, classes_eqv_classes⟩

theorem is_partition.pairwise_disjoint {c : Set (Set α)} (hc : is_partition c) : c.pairwise_disjoint id :=
  eqv_classes_disjoint hc.2

theorem is_partition.sUnion_eq_univ {c : Set (Set α)} (hc : is_partition c) : ⋃₀c = Set.Univ :=
  Set.eq_univ_of_forall$
    fun x =>
      Set.mem_sUnion.2$
        let ⟨t, ht⟩ := hc.2 x
        ⟨t,
          by 
            clearAuxDecl <;> finish⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
  theorem
    exists_of_mem_partition
    { c : Set Set α } ( hc : is_partition c ) { s } ( hs : s ∈ c ) : ∃ y , s = { x | mk_classes c hc . 2 . Rel x y }
    := let ⟨ y , hy ⟩ := nonempty_of_mem_partition hc hs ⟨ y , eq_eqv_class_of_mem hc . 2 hs hy ⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mk_classes (c : Set (Set α)) (hc : is_partition c) : (mk_classes c hc.2).Classes = c :=
  Set.ext$
    fun s =>
      ⟨fun ⟨y, hs⟩ =>
          (hc.2 y).elim2$
            fun b hm hb hy =>
              by 
                rwa
                  [show s = b from
                    hs.symm ▸
                      Set.ext
                        fun x =>
                          ⟨fun hx => symm' (mk_classes c hc.2) hx b hm hb,
                            fun hx b' hc' hx' => eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩],
        exists_of_mem_partition hc⟩

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance partition.le : LE (Subtype (@is_partition α)) :=
  ⟨fun x y => mk_classes x.1 x.2.2 ≤ mk_classes y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance partition.partial_order : PartialOrderₓ (Subtype (@is_partition α)) :=
  { le := · ≤ ·, lt := fun x y => x ≤ y ∧ ¬y ≤ x, le_refl := fun _ => @le_reflₓ (Setoidₓ α) _ _,
    le_trans := fun _ _ _ => @le_transₓ (Setoidₓ α) _ _ _ _, lt_iff_le_not_le := fun _ _ => Iff.rfl,
    le_antisymm :=
      fun x y hx hy =>
        let h := @le_antisymmₓ (Setoidₓ α) _ _ _ hx hy 
        by 
          rw [Subtype.ext_iff_val, ←classes_mk_classes x.1 x.2, ←classes_mk_classes y.1 y.2, h] }

variable (α)

/-- The order-preserving bijection between equivalence relations on a type `α`, and
  partitions of `α` into subsets. -/
protected def partition.order_iso : Setoidₓ α ≃o { C : Set (Set α) // is_partition C } :=
  { toFun := fun r => ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩, invFun := fun C => mk_classes C.1 C.2.2,
    left_inv := mk_classes_classes,
    right_inv :=
      fun C =>
        by 
          rw [Subtype.ext_iff_val, ←classes_mk_classes C.1 C.2],
    map_rel_iff' :=
      fun r s =>
        by 
          convRHS => rw [←mk_classes_classes r, ←mk_classes_classes s]
          rfl }

variable {α}

/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
instance partition.complete_lattice : CompleteLattice (Subtype (@is_partition α)) :=
  GaloisInsertion.liftCompleteLattice$
    @OrderIso.toGaloisInsertion _ (Subtype (@is_partition α)) _ (PartialOrderₓ.toPreorder _)$ partition.order_iso α

end Partition

end Setoidₓ

/-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
`s : ι → set α`.

`indexed_partition.index` sends an element to its index, while `indexed_partition.some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not needed, then
`setoid.ker index` by itself may be sufficient. -/
structure IndexedPartition {ι α : Type _} (s : ι → Set α) where 
  eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j 
  some : ι → α 
  some_mem : ∀ i, some i ∈ s i 
  index : α → ι 
  mem_index : ∀ x, x ∈ s (index x)

/-- The non-constructive constructor for `indexed_partition`. -/
noncomputable def IndexedPartition.mk' {ι α : Type _} (s : ι → Set α) (dis : ∀ i j, i ≠ j → Disjoint (s i) (s j))
  (nonempty : ∀ i, (s i).Nonempty) (ex : ∀ x, ∃ i, x ∈ s i) : IndexedPartition s :=
  { eq_of_mem := fun x i j hxi hxj => Classical.by_contradiction$ fun h => dis _ _ h ⟨hxi, hxj⟩,
    some := fun i => (Nonempty i).some, some_mem := fun i => (Nonempty i).some_spec, index := fun x => (ex x).some,
    mem_index := fun x => (ex x).some_spec }

namespace IndexedPartition

open Set

variable {ι α : Type _} {s : ι → Set α} (hs : IndexedPartition s)

/-- On a unique index set there is the obvious trivial partition -/
instance [Unique ι] [Inhabited α] : Inhabited (IndexedPartition fun i : ι => (Set.Univ : Set α)) :=
  ⟨{ eq_of_mem := fun x i j hi hj => Subsingleton.elimₓ _ _, some := fun i => default α, some_mem := Set.mem_univ,
      index := fun a => default ι, mem_index := Set.mem_univ }⟩

attribute [simp] some_mem mem_index

include hs

theorem exists_mem (x : α) : ∃ i, x ∈ s i :=
  ⟨hs.index x, hs.mem_index x⟩

theorem Union : (⋃ i, s i) = univ :=
  by 
    ext x 
    simp [hs.exists_mem x]

theorem Disjoint : ∀ {i j}, i ≠ j → Disjoint (s i) (s j) :=
  fun i j h x ⟨hxi, hxj⟩ => h (hs.eq_of_mem hxi hxj)

theorem mem_iff_index_eq {x i} : x ∈ s i ↔ hs.index x = i :=
  ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem Eq i : s i = { x | hs.index x = i } := Set.ext $ fun _ => hs.mem_iff_index_eq

/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
protected abbrev Setoidₓ (hs : IndexedPartition s) : Setoidₓ α :=
  Setoidₓ.ker hs.index

@[simp]
theorem index_some (i : ι) : hs.index (hs.some i) = i :=
  (mem_iff_index_eq _).1$ hs.some_mem i

theorem some_index (x : α) : hs.setoid.rel (hs.some (hs.index x)) x :=
  hs.index_some (hs.index x)

/-- The quotient associated to an indexed partition. -/
protected def Quotientₓ :=
  Quotientₓ hs.setoid

/-- The projection onto the quotient associated to an indexed partition. -/
def proj : α → hs.quotient :=
  Quotientₓ.mk'

instance [Inhabited α] : Inhabited hs.quotient :=
  ⟨hs.proj (default α)⟩

theorem proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
  Quotientₓ.eq_rel

@[simp]
theorem proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
  Quotientₓ.eq'.2 (hs.some_index x)

/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
def equiv_quotient : ι ≃ hs.quotient :=
  (Setoidₓ.quotientKerEquivOfRightInverse hs.index hs.some$ hs.index_some).symm

@[simp]
theorem equiv_quotient_index_apply (x : α) : hs.equiv_quotient (hs.index x) = hs.proj x :=
  hs.proj_eq_iff.mpr (some_index hs x)

@[simp]
theorem equiv_quotient_symm_proj_apply (x : α) : hs.equiv_quotient.symm (hs.proj x) = hs.index x :=
  rfl

theorem equiv_quotient_index : hs.equiv_quotient ∘ hs.index = hs.proj :=
  funext hs.equiv_quotient_index_apply

/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. This is a computable version of `quotient.out'` using `indexed_partition.some`. -/
def out : hs.quotient ↪ α :=
  hs.equiv_quotient.symm.to_embedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

/-- This lemma is analogous to `quotient.mk_out'`. -/
@[simp]
theorem out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
  rfl

/-- The indices of `quotient.out'` and `indexed_partition.out` are equal. -/
theorem index_out' (x : hs.quotient) : hs.index x.out' = hs.index (hs.out x) :=
  Quotientₓ.induction_on' x$ fun x => (Setoidₓ.ker_apply_mk_out' x).trans (hs.index_some _).symm

/-- This lemma is analogous to `quotient.out_eq'`. -/
@[simp]
theorem proj_out (x : hs.quotient) : hs.proj (hs.out x) = x :=
  Quotientₓ.induction_on' x$ fun x => Quotientₓ.sound'$ hs.some_index x

theorem class_of {x : α} : SetOf (hs.setoid.rel x) = s (hs.index x) :=
  Set.ext$ fun y => eq_comm.trans hs.mem_iff_index_eq.symm

theorem proj_fiber (x : hs.quotient) : hs.proj ⁻¹' {x} = s (hs.equiv_quotient.symm x) :=
  Quotientₓ.induction_on' x$
    fun x =>
      by 
        ext y 
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hs.mem_iff_index_eq]
        exact Quotientₓ.eq'

end IndexedPartition

