import Mathbin.Data.Finsupp.Order

/-!
# Equivalence between `multiset` and `ℕ`-valued finitely supported functions

This defines `finsupp.to_multiset` the equivalence between `α →₀ ℕ` and `multiset α`, along
with `multiset.to_finsupp` the reverse equivalence and `finsupp.order_iso_multiset` the equivalence
promoted to an order isomorphism.
-/


open Finset

open_locale BigOperators Classical

noncomputable section

variable {α β ι : Type _}

namespace Finsupp

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def to_multiset : (α →₀ ℕ) ≃+ Multiset α where
  toFun := fun f => f.sum fun a n => n • {a}
  invFun := fun s =>
    ⟨s.to_finset, fun a => s.count a, fun a => by
      simp ⟩
  left_inv := fun f =>
    ext $ fun a => by
      simp only [Sum, Multiset.count_sum', Multiset.count_singleton, mul_boole, coe_mk, mem_support_iff,
        Multiset.count_nsmul, Finset.sum_ite_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
  right_inv := fun s => by
    simp only [Sum, coe_mk, Multiset.to_finset_sum_count_nsmul_eq]
  map_add' := fun f g => sum_add_index (fun a => zero_nsmul _) fun a => add_nsmul _

theorem to_multiset_zero : (0 : α →₀ ℕ).toMultiset = 0 :=
  rfl

theorem to_multiset_add (m n : α →₀ ℕ) : (m + n).toMultiset = m.to_multiset + n.to_multiset :=
  to_multiset.map_add m n

theorem to_multiset_apply (f : α →₀ ℕ) : f.to_multiset = f.sum fun a n => n • {a} :=
  rfl

@[simp]
theorem to_multiset_symm_apply [DecidableEq α] (s : Multiset α) (x : α) : Finsupp.toMultiset.symm s x = s.count x := by
  convert rfl

@[simp]
theorem to_multiset_single (a : α) (n : ℕ) : to_multiset (single a n) = n • {a} := by
  rw [to_multiset_apply, sum_single_index] <;> apply zero_nsmul

theorem to_multiset_sum {f : ι → α →₀ ℕ} (s : Finset ι) :
    Finsupp.toMultiset (∑ i in s, f i) = ∑ i in s, Finsupp.toMultiset (f i) :=
  AddEquiv.map_sum _ _ _

theorem to_multiset_sum_single (s : Finset ι) (n : ℕ) : Finsupp.toMultiset (∑ i in s, single i n) = n • s.val := by
  simp_rw [to_multiset_sum, Finsupp.to_multiset_single, sum_nsmul, sum_multiset_singleton]

theorem card_to_multiset (f : α →₀ ℕ) : f.to_multiset.card = f.sum fun a => id := by
  simp [to_multiset_apply, AddMonoidHom.map_finsupp_sum, Function.id_def]

theorem to_multiset_map (f : α →₀ ℕ) (g : α → β) : f.to_multiset.map g = (f.map_domain g).toMultiset := by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.map_zero, map_domain_zero, to_multiset_zero]
    
  · intro a n f _ _ ih
    rw [to_multiset_add, Multiset.map_add, ih, map_domain_add, map_domain_single, to_multiset_single, to_multiset_add,
      to_multiset_single, ← Multiset.coe_map_add_monoid_hom, (Multiset.mapAddMonoidHom g).map_nsmul]
    rfl
    

@[simp]
theorem prod_to_multiset [CommMonoidₓ α] (f : α →₀ ℕ) : f.to_multiset.prod = f.prod fun a n => a ^ n := by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
    
  · intro a n f _ _ ih
    rw [to_multiset_add, Multiset.prod_add, ih, to_multiset_single, Finsupp.prod_add_index, Finsupp.prod_single_index,
      Multiset.prod_nsmul, Multiset.prod_singleton]
    · exact pow_zeroₓ a
      
    · exact pow_zeroₓ
      
    · exact pow_addₓ
      
    

@[simp]
theorem to_finset_to_multiset [DecidableEq α] (f : α →₀ ℕ) : f.to_multiset.to_finset = f.support := by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.to_finset_zero, support_zero]
    
  · intro a n f ha hn ih
    rw [to_multiset_add, Multiset.to_finset_add, ih, to_multiset_single, support_add_eq, support_single_ne_zero hn,
      Multiset.to_finset_nsmul _ _ hn, Multiset.to_finset_singleton]
    refine' Disjoint.mono_left support_single_subset _
    rwa [Finset.disjoint_singleton_left]
    

@[simp]
theorem count_to_multiset [DecidableEq α] (f : α →₀ ℕ) (a : α) : f.to_multiset.count a = f a :=
  calc
    f.to_multiset.count a = f.sum fun x n => (n • {x} : Multiset α).count a :=
      (Multiset.countAddMonoidHom a).map_sum _ f.support
    _ = f.sum fun x n => n * ({x} : Multiset α).count a := by
      simp only [Multiset.count_nsmul]
    _ = f a * ({a} : Multiset α).count a :=
      sum_eq_single _
        (fun a' _ H => by
          simp only [Multiset.count_singleton, if_false, H.symm, mul_zero])
        fun H => by
        simp only [not_mem_support_iff.1 H, zero_mul]
    _ = f a := by
      rw [Multiset.count_singleton_self, mul_oneₓ]
    

@[simp]
theorem mem_to_multiset (f : α →₀ ℕ) (i : α) : i ∈ f.to_multiset ↔ i ∈ f.support := by
  rw [← Multiset.count_ne_zero, Finsupp.count_to_multiset, Finsupp.mem_support_iff]

end Finsupp

namespace Multiset

/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def to_finsupp : Multiset α ≃+ (α →₀ ℕ) :=
  Finsupp.toMultiset.symm

@[simp]
theorem to_finsupp_support [DecidableEq α] (s : Multiset α) : s.to_finsupp.support = s.to_finset := by
  convert rfl

@[simp]
theorem to_finsupp_apply [DecidableEq α] (s : Multiset α) (a : α) : to_finsupp s a = s.count a := by
  convert rfl

theorem to_finsupp_zero : to_finsupp (0 : Multiset α) = 0 :=
  AddEquiv.map_zero _

theorem to_finsupp_add (s t : Multiset α) : to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
  to_finsupp.map_add s t

@[simp]
theorem to_finsupp_singleton (a : α) : to_finsupp ({a} : Multiset α) = Finsupp.single a 1 :=
  Finsupp.toMultiset.symm_apply_eq.2 $ by
    simp

@[simp]
theorem to_finsupp_to_multiset (s : Multiset α) : s.to_finsupp.to_multiset = s :=
  Finsupp.toMultiset.apply_symm_apply s

theorem to_finsupp_eq_iff {s : Multiset α} {f : α →₀ ℕ} : s.to_finsupp = f ↔ s = f.to_multiset :=
  Finsupp.toMultiset.symm_apply_eq

end Multiset

@[simp]
theorem Finsupp.to_multiset_to_finsupp (f : α →₀ ℕ) : f.to_multiset.to_finsupp = f :=
  Finsupp.toMultiset.symm_apply_apply f

/-! ### As an order isomorphism -/


namespace Finsupp

/-- `finsupp.to_multiset` as an order isomorphism. -/
def order_iso_multiset : (ι →₀ ℕ) ≃o Multiset ι where
  toEquiv := to_multiset.toEquiv
  map_rel_iff' := fun f g => by
    simp [Multiset.le_iff_count, le_def]

@[simp]
theorem coe_order_iso_multiset : ⇑@order_iso_multiset ι = to_multiset :=
  rfl

@[simp]
theorem coe_order_iso_multiset_symm : ⇑(@order_iso_multiset ι).symm = Multiset.toFinsupp :=
  rfl

theorem to_multiset_strict_mono : StrictMono (@to_multiset ι) :=
  (@order_iso_multiset ι).StrictMono

theorem sum_id_lt_of_lt (m n : ι →₀ ℕ) (h : m < n) : (m.sum fun _ => id) < n.sum fun _ => id := by
  rw [← card_to_multiset, ← card_to_multiset]
  apply Multiset.card_lt_of_lt
  exact to_multiset_strict_mono h

variable (ι)

/-- The order on `ι →₀ ℕ` is well-founded. -/
theorem lt_wf : WellFounded (@LT.lt (ι →₀ ℕ) _) :=
  Subrelation.wfₓ sum_id_lt_of_lt $ InvImage.wfₓ _ Nat.lt_wf

end Finsupp

theorem Multiset.to_finsupp_strict_mono : StrictMono (@Multiset.toFinsupp ι) :=
  (@Finsupp.orderIsoMultiset ι).symm.StrictMono

