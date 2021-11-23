import Mathbin.Data.Nat.Enat 
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `conditionally_complete_linear_order_bot` structure on `ℕ`;
* define a `complete_linear_order` structure on `enat`;
* prove a few lemmas about `supr`/`infi`/`set.Union`/`set.Inter` and natural numbers.
-/


open Set

namespace Nat

open_locale Classical

noncomputable instance  : HasInfₓ ℕ :=
  ⟨fun s => if h : ∃ n, n ∈ s then @Nat.findₓ (fun n => n ∈ s) _ h else 0⟩

noncomputable instance  : HasSupₓ ℕ :=
  ⟨fun s => if h : ∃ n, ∀ a _ : a ∈ s, a ≤ n then @Nat.findₓ (fun n => ∀ a _ : a ∈ s, a ≤ n) _ h else 0⟩

theorem Inf_def {s : Set ℕ} (h : s.nonempty) : Inf s = @Nat.findₓ (fun n => n ∈ s) _ h :=
  dif_pos _

theorem Sup_def {s : Set ℕ} (h : ∃ n, ∀ a _ : a ∈ s, a ≤ n) : Sup s = @Nat.findₓ (fun n => ∀ a _ : a ∈ s, a ≤ n) _ h :=
  dif_pos _

-- error in Data.Nat.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem Inf_eq_zero
{s : set exprℕ()} : «expr ↔ »(«expr = »(Inf s, 0), «expr ∨ »(«expr ∈ »(0, s), «expr = »(s, «expr∅»()))) :=
begin
  cases [expr eq_empty_or_nonempty s] [],
  { subst [expr h],
    simp [] [] ["only"] ["[", expr or_true, ",", expr eq_self_iff_true, ",", expr iff_true, ",", expr Inf, ",", expr has_Inf.Inf, ",", expr mem_empty_eq, ",", expr exists_false, ",", expr dif_neg, ",", expr not_false_iff, "]"] [] [] },
  { have [] [] [":=", expr ne_empty_iff_nonempty.mpr h],
    simp [] [] ["only"] ["[", expr this, ",", expr or_false, ",", expr nat.Inf_def, ",", expr h, ",", expr nat.find_eq_zero, "]"] [] [] }
end

@[simp]
theorem Inf_empty : Inf ∅ = 0 :=
  by 
    rw [Inf_eq_zero]
    right 
    rfl

theorem Inf_mem {s : Set ℕ} (h : s.nonempty) : Inf s ∈ s :=
  by 
    rw [Nat.Inf_def h]
    exact Nat.find_specₓ h

theorem not_mem_of_lt_Inf {s : Set ℕ} {m : ℕ} (hm : m < Inf s) : m ∉ s :=
  by 
    cases eq_empty_or_nonempty s
    ·
      subst h 
      apply not_mem_empty
    ·
      rw [Nat.Inf_def h] at hm 
      exact Nat.find_minₓ h hm

protected theorem Inf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : Inf s ≤ m :=
  by 
    rw [Nat.Inf_def ⟨m, hm⟩]
    exact Nat.find_min'ₓ ⟨m, hm⟩ hm

-- error in Data.Nat.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nonempty_of_pos_Inf {s : set exprℕ()} (h : «expr < »(0, Inf s)) : s.nonempty :=
begin
  by_contradiction [ident contra],
  rw [expr set.not_nonempty_iff_eq_empty] ["at", ident contra],
  have [ident h'] [":", expr «expr ≠ »(Inf s, 0)] [],
  { exact [expr ne_of_gt h] },
  apply [expr h'],
  rw [expr nat.Inf_eq_zero] [],
  right,
  assumption
end

theorem nonempty_of_Inf_eq_succ {s : Set ℕ} {k : ℕ} (h : Inf s = k+1) : s.nonempty :=
  nonempty_of_pos_Inf (h.symm ▸ succ_pos k : Inf s > 0)

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.nonempty)
  (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (Inf s) :=
  ext fun n => ⟨fun H => Nat.Inf_le H, fun H => hs' (Inf s) n H (Inf_mem hs)⟩

theorem Inf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) (k : ℕ) :
  (Inf s = k+1) ↔ (k+1) ∈ s ∧ k ∉ s :=
  by 
    split 
    ·
      intro H 
      rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_Inf_eq_succ H) hs, H, mem_Ici, mem_Ici]
      exact ⟨le_reflₓ _, k.not_succ_le_self⟩
    ·
      rintro ⟨H, H'⟩
      rw [Inf_def (⟨_, H⟩ : s.nonempty), find_eq_iff]
      exact ⟨H, fun n hnk hns => H'$ hs n k (lt_succ_iff.mp hnk) hns⟩

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance  : Lattice ℕ :=
  latticeOfLinearOrder

noncomputable instance  : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (latticeOfLinearOrder : Lattice ℕ), (inferInstance : LinearOrderₓ ℕ) with sup := Sup,
    inf := Inf,
    le_cSup :=
      fun s a hb ha =>
        by 
          rw [Sup_def hb] <;> revert a ha <;> exact @Nat.find_specₓ _ _ hb,
    cSup_le :=
      fun s a hs ha =>
        by 
          rw [Sup_def ⟨a, ha⟩] <;> exact Nat.find_min'ₓ _ ha,
    le_cInf :=
      fun s a hs hb =>
        by 
          rw [Inf_def hs] <;> exact hb (@Nat.find_specₓ (fun n => n ∈ s) _ _),
    cInf_le :=
      fun s a hb ha =>
        by 
          rw [Inf_def ⟨a, ha⟩] <;> exact Nat.find_min'ₓ _ ha,
    cSup_empty :=
      by 
        simp only [Sup_def, Set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff, exists_const]
        apply bot_unique (Nat.find_min'ₓ _ _)
        trivial }

-- error in Data.Nat.Lattice: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Inf_add
{n : exprℕ()}
{p : exprℕ() → exprProp()}
(hn : «expr ≤ »(n, Inf {m | p m})) : «expr = »(«expr + »(Inf {m | p «expr + »(m, n)}, n), Inf {m | p m}) :=
begin
  obtain [ident h, "|", "⟨", ident m, ",", ident hm, "⟩", ":=", expr {m | p «expr + »(m, n)}.eq_empty_or_nonempty],
  { rw ["[", expr h, ",", expr nat.Inf_empty, ",", expr zero_add, "]"] [],
    obtain [ident hnp, "|", ident hnp, ":=", expr hn.eq_or_lt],
    { exact [expr hnp] },
    suffices [ident hp] [":", expr p «expr + »(«expr - »(Inf {m | p m}, n), n)],
    { exact [expr (h.subset hp).elim] },
    rw [expr tsub_add_cancel_of_le hn] [],
    exact [expr Inf_mem «expr $ »(nonempty_of_pos_Inf, n.zero_le.trans_lt hnp)] },
  { have [ident hp] [":", expr «expr∃ , »((n), «expr ∈ »(n, {m | p m}))] [":=", expr ⟨_, hm⟩],
    rw ["[", expr nat.Inf_def ⟨m, hm⟩, ",", expr nat.Inf_def hp, "]"] [],
    rw ["[", expr nat.Inf_def hp, "]"] ["at", ident hn],
    exact [expr find_add hn] }
end

theorem Inf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < Inf { m | p m }) : (Inf { m | p m }+n) = Inf { m | p (m - n) } :=
  by 
    convert Inf_add _
    ·
      simpRw [add_tsub_cancel_right]
    obtain ⟨m, hm⟩ := nonempty_of_pos_Inf h 
    refine'
      le_cInf ⟨m+n, _⟩
        fun b hb => le_of_not_ltₓ$ fun hbn => ne_of_mem_of_not_mem _ (not_mem_of_lt_Inf h) (tsub_eq_zero_of_le hbn.le)
    ·
      dsimp 
      rwa [add_tsub_cancel_right]
    ·
      exact hb

section 

variable{α : Type _}[CompleteLattice α]

theorem supr_lt_succ (u : ℕ → α) (n : ℕ) : (⨆(k : _)(_ : k < n+1), u k) = (⨆(k : _)(_ : k < n), u k)⊔u n :=
  by 
    simp [Nat.lt_succ_iff_lt_or_eq, supr_or, supr_sup_eq]

theorem supr_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆(k : _)(_ : k < n+1), u k) = u 0⊔⨆(k : _)(_ : k < n), u (k+1) :=
  by 
    rw [←sup_supr_nat_succ]
    simp 

theorem infi_lt_succ (u : ℕ → α) (n : ℕ) : (⨅(k : _)(_ : k < n+1), u k) = (⨅(k : _)(_ : k < n), u k)⊓u n :=
  @supr_lt_succ (OrderDual α) _ _ _

theorem infi_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅(k : _)(_ : k < n+1), u k) = u 0⊓⨅(k : _)(_ : k < n), u (k+1) :=
  @supr_lt_succ' (OrderDual α) _ _ _

end 

end Nat

namespace Set

variable{α : Type _}

theorem bUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋃(k : _)(_ : k < n+1), u k) = (⋃(k : _)(_ : k < n), u k) ∪ u n :=
  Nat.supr_lt_succ u n

theorem bUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋃(k : _)(_ : k < n+1), u k) = u 0 ∪ ⋃(k : _)(_ : k < n), u (k+1) :=
  Nat.supr_lt_succ' u n

theorem bInter_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋂(k : _)(_ : k < n+1), u k) = (⋂(k : _)(_ : k < n), u k) ∩ u n :=
  Nat.infi_lt_succ u n

theorem bInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋂(k : _)(_ : k < n+1), u k) = u 0 ∩ ⋂(k : _)(_ : k < n), u (k+1) :=
  Nat.infi_lt_succ' u n

end Set

namespace Enat

open_locale Classical

noncomputable instance  : CompleteLinearOrder Enat :=
  { Enat.linearOrder, with_top_order_iso.symm.toGaloisInsertion.liftCompleteLattice with  }

end Enat

