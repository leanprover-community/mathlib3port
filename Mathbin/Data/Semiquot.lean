import Mathbin.Data.Set.Lattice

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/


/-- A member of `semiquot α` is classically a nonempty `set α`,
  and in the VM is represented by an element of `α`; the relation
  between these is that the VM element is required to be a member
  of the set `s`. The specific element of `s` that the VM computes
  is hidden by a quotient construction, allowing for the representation
  of nondeterministic functions. -/
structure Semiquot.{u}(α : Type _) where mk' :: 
  S : Set α 
  val : Trunc («expr↥ » s)

namespace Semiquot

variable{α : Type _}{β : Type _}

instance  : HasMem α (Semiquot α) :=
  ⟨fun a q => a ∈ q.s⟩

/-- Construct a `semiquot α` from `h : a ∈ s` where `s : set α`. -/
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩

theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s :=
  ⟨congr_argₓ _,
    fun h =>
      by 
        cases q₁ <;> cases q₂ <;> congr <;> exact h⟩

theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff

theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, h₂⟩ := q.2.exists_rep
  ⟨a, h⟩

theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl

theorem Nonempty (q : Semiquot α) : q.s.nonempty :=
  q.exists_mem

/-- `pure a` is `a` reinterpreted as an unspecified element of `{a}`. -/
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)

@[simp]
theorem mem_pure' {a b : α} : a ∈ Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff

/-- Replace `s` in a `semiquot` with a superset. -/
def blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩

/-- Replace `s` in a `q : semiquot α` with a union `s ∪ q.s` -/
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (Set.subset_union_right s q.s)

theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s ⊆ s) : blur s q = blur' q h :=
  by 
    unfold blur <;> congr <;> exact Set.union_eq_self_of_subset_right h

@[simp]
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) {a : α} : a ∈ blur' q h ↔ a ∈ s :=
  Iff.rfl

/-- Convert a `trunc α` to a `semiquot α`. -/
def of_trunc (q : Trunc α) : Semiquot α :=
  ⟨Set.Univ, q.map fun a => ⟨a, trivialₓ⟩⟩

/-- Convert a `semiquot α` to a `trunc α`. -/
def to_trunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val

/-- If `f` is a constant on `q.s`, then `q.lift_on f` is the value of `f`
at any point of `q`. -/
def lift_on (q : Semiquot α) (f : α → β) (h : ∀ a b _ : a ∈ q _ : b ∈ q, f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ _ x.2 y.2

theorem lift_on_of_mem (q : Semiquot α) (f : α → β) (h : ∀ a b _ : a ∈ q _ : b ∈ q, f a = f b) (a : α) (aq : a ∈ q) :
  lift_on q f h = f a :=
  by 
    revert h <;> rw [eq_mk_of_mem aq] <;> intro  <;> rfl

/-- Apply a function to the unknown value stored in a `semiquot α`. -/
def map (f : α → β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩

@[simp]
theorem mem_map (f : α → β) (q : Semiquot α) (b : β) : b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b :=
  Set.mem_image _ _ _

/-- Apply a function returning a `semiquot` to a `semiquot`. -/
def bind (q : Semiquot α) (f : α → Semiquot β) : Semiquot β :=
  ⟨⋃(a : _)(_ : a ∈ q.1), (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_bUnion a.2 b.2⟩⟩

@[simp]
theorem mem_bind (q : Semiquot α) (f : α → Semiquot β) (b : β) : b ∈ bind q f ↔ ∃ (a : _)(_ : a ∈ q), b ∈ f a :=
  Set.mem_bUnion_iff

instance  : Monadₓ Semiquot :=
  { pure := @Semiquot.pure, map := @Semiquot.map, bind := @Semiquot.bind }

@[simp]
theorem map_def {β} : (· <$> · : (α → β) → Semiquot α → Semiquot β) = map :=
  rfl

@[simp]
theorem bind_def {β} : (· >>= · : Semiquot α → (α → Semiquot β) → Semiquot β) = bind :=
  rfl

@[simp]
theorem mem_pure {a b : α} : a ∈ (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff

theorem mem_pure_self (a : α) : a ∈ (pure a : Semiquot α) :=
  Set.mem_singleton a

@[simp]
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff

instance  : IsLawfulMonad Semiquot :=
  { pure_bind :=
      fun α β x f =>
        ext.2$
          by 
            simp ,
    bind_assoc :=
      fun α β γ s f g =>
        ext.2$
          by 
            simp  <;>
              exact
                fun c =>
                  ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩, fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩,
    id_map :=
      fun α q =>
        ext.2$
          by 
            simp ,
    bind_pure_comp_eq_map :=
      fun α β f s =>
        ext.2$
          by 
            simp [eq_comm] }

instance  : LE (Semiquot α) :=
  ⟨fun s t => s.s ⊆ t.s⟩

instance  : PartialOrderₓ (Semiquot α) :=
  { le := fun s t => ∀ ⦃x⦄, x ∈ s → x ∈ t, le_refl := fun s => Set.Subset.refl _,
    le_trans := fun s t u => Set.Subset.trans, le_antisymm := fun s t h₁ h₂ => ext_s.2 (Set.Subset.antisymm h₁ h₂) }

instance  : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with sup := fun s => blur s.s, le_sup_left := fun s t => Set.subset_union_left _ _,
    le_sup_right := fun s t => Set.subset_union_right _ _, sup_le := fun s t u => Set.union_subset }

@[simp]
theorem pure_le {a : α} {s : Semiquot α} : pure a ≤ s ↔ a ∈ s :=
  Set.singleton_subset_iff

/-- Assert that a `semiquot` contains only one possible value. -/
def is_pure (q : Semiquot α) : Prop :=
  ∀ a b _ : a ∈ q _ : b ∈ q, a = b

/-- Extract the value from a `is_pure` semiquotient. -/
def get (q : Semiquot α) (h : q.is_pure) : α :=
  lift_on q id h

theorem get_mem {q : Semiquot α} p : get q p ∈ q :=
  let ⟨a, h⟩ := exists_mem q 
  by 
    unfold get <;> rw [lift_on_of_mem q _ _ a h] <;> exact h

theorem eq_pure {q : Semiquot α} p : q = pure (get q p) :=
  ext.2$
    fun a =>
      by 
        simp  <;> exact ⟨fun h => p _ _ h (get_mem _), fun e => e.symm ▸ get_mem _⟩

@[simp]
theorem pure_is_pure (a : α) : is_pure (pure a)
| b, c, ab, ac =>
  by 
    simp  at ab ac 
    cc

theorem is_pure_iff {s : Semiquot α} : is_pure s ↔ ∃ a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨a, e⟩ => e.symm ▸ pure_is_pure _⟩

theorem is_pure.mono {s t : Semiquot α} (st : s ≤ t) (h : is_pure t) : is_pure s
| a, b, as, bs => h _ _ (st as) (st bs)

theorem is_pure.min {s t : Semiquot α} (h : is_pure t) : s ≤ t ↔ s = t :=
  ⟨fun st =>
      le_antisymmₓ st$
        by 
          rw [eq_pure h, eq_pure (h.mono st)] <;> simp  <;> exact h _ _ (get_mem _) (st$ get_mem _),
    le_of_eqₓ⟩

theorem is_pure_of_subsingleton [Subsingleton α] (q : Semiquot α) : is_pure q
| a, b, aq, bq => Subsingleton.elimₓ _ _

/-- `univ : semiquot α` represents an unspecified element of `univ : set α`. -/
def univ [Inhabited α] : Semiquot α :=
  mk$ Set.mem_univ (default _)

instance  [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩

@[simp]
theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
  @Set.mem_univ α

@[congr]
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2$
    by 
      simp 

@[simp]
theorem is_pure_univ [Inhabited α] : @is_pure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a b trivialₓ trivialₓ⟩, fun ⟨h⟩ a b _ _ => h a b⟩

instance  [Inhabited α] : OrderTop (Semiquot α) :=
  { top := univ, le_top := fun s => Set.subset_univ _ }

instance  [Inhabited α] : SemilatticeSupTop (Semiquot α) :=
  { Semiquot.orderTop, Semiquot.semilatticeSup with  }

end Semiquot

