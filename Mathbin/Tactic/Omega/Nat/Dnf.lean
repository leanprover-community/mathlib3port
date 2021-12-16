import Mathbin.Data.List.ProdSigma 
import Mathbin.Tactic.Omega.Clause 
import Mathbin.Tactic.Omega.Nat.Form

/-!
# DNF transformation
-/


namespace Omega

namespace Nat

open_locale Omega.Nat

@[simp]
def dnf_core : preform → List clause
| p ∨* q => dnf_core p ++ dnf_core q
| p ∧* q => (List.product (dnf_core p) (dnf_core q)).map fun pq => clause.append pq.fst pq.snd
| t =* s => [([term.sub (canonize s) (canonize t)], [])]
| t ≤* s => [([], [term.sub (canonize s) (canonize t)])]
| ¬* _ => []

-- ././Mathport/Syntax/Translate/Basic.lean:686:4: warning: unsupported (TODO): `[tacs]
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » dnf_core p)
theorem exists_clause_holds_core {v : Nat → Nat} :
  ∀ {p : preform},
    p.neg_free → p.sub_free → p.holds v → ∃ (c : _)(_ : c ∈ dnf_core p), clause.holds (fun x => ↑v x) c :=
  by 
    runTac 
      preform.induce sorry
    ·
      apply List.exists_mem_cons_ofₓ 
      constructor 
      rw [List.forall_mem_singleton]
      cases' h0 with ht hs 
      simp only [val_canonize ht, val_canonize hs, term.val_sub, preform.holds, sub_eq_add_neg] at *
      rw [h2, add_neg_selfₓ]
      apply List.forall_mem_nil
    ·
      apply List.exists_mem_cons_ofₓ 
      constructor 
      apply List.forall_mem_nil 
      rw [List.forall_mem_singleton]
      simp only [val_canonize h0.left, val_canonize h0.right, term.val_sub, preform.holds, sub_eq_add_neg] at *
      rw [←sub_eq_add_neg, le_sub, sub_zero, Int.coe_nat_le]
      assumption
    ·
      cases h1
    ·
      cases' h2 with h2 h2 <;>
          [·
            cases' ihp h1.left h0.left h2 with c h3,
          ·
            cases' ihq h1.right h0.right h2 with c h3] <;>
        cases' h3 with h3 h4 <;> refine' ⟨c, list.mem_append.elim_right _, h4⟩ <;> [left, right] <;> assumption
    ·
      rcases ihp h1.left h0.left h2.left with ⟨cp, hp1, hp2⟩
      rcases ihq h1.right h0.right h2.right with ⟨cq, hq1, hq2⟩
      refine' ⟨clause.append cp cq, ⟨_, clause.holds_append hp2 hq2⟩⟩
      simp only [dnf_core, List.mem_mapₓ]
      refine' ⟨(cp, cq), ⟨_, rfl⟩⟩
      rw [List.mem_product]
      constructor <;> assumption

def term.vars_core (is : List Int) : List Bool :=
  is.map fun i => if i = 0 then ff else tt

/-- Return a list of bools that encodes which variables have nonzero coefficients -/
def term.vars (t : term) : List Bool :=
  term.vars_core t.snd

def bools.or : List Bool → List Bool → List Bool
| [], bs2 => bs2
| bs1, [] => bs1
| b1 :: bs1, b2 :: bs2 => (b1 || b2) :: bools.or bs1 bs2

/-- Return a list of bools that encodes which variables have nonzero coefficients in any one of the
input terms. -/
def terms.vars : List term → List Bool
| [] => []
| t :: ts => bools.or (term.vars t) (terms.vars ts)

open_locale List.Func

def nonneg_consts_core : Nat → List Bool → List term
| _, [] => []
| k, ff :: bs => nonneg_consts_core (k+1) bs
| k, tt :: bs => ⟨0, [] {k ↦ 1}⟩ :: nonneg_consts_core (k+1) bs

def nonneg_consts (bs : List Bool) : List term :=
  nonneg_consts_core 0 bs

def nonnegate : clause → clause
| (eqs, les) =>
  let xs := terms.vars eqs 
  let ys := terms.vars les 
  let bs := bools.or xs ys
  (eqs, nonneg_consts bs ++ les)

/-- DNF transformation -/
def dnf (p : preform) : List clause :=
  (dnf_core p).map nonnegate

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » nonneg_consts_core m bs)
theorem holds_nonneg_consts_core {v : Nat → Int} (h1 : ∀ x, 0 ≤ v x) :
  ∀ m bs, ∀ t _ : t ∈ nonneg_consts_core m bs, 0 ≤ term.val v t
| _, [] =>
  fun _ h2 =>
    by 
      cases h2
| k, ff :: bs => holds_nonneg_consts_core (k+1) bs
| k, tt :: bs =>
  by 
    simp only [nonneg_consts_core]
    rw [List.forall_mem_consₓ]
    constructor
    ·
      simp only [term.val, one_mulₓ, zero_addₓ, coeffs.val_set]
      apply h1
    ·
      apply holds_nonneg_consts_core (k+1) bs

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » nonneg_consts bs)
theorem holds_nonneg_consts {v : Nat → Int} {bs : List Bool} :
  (∀ x, 0 ≤ v x) → ∀ t _ : t ∈ nonneg_consts bs, 0 ≤ term.val v t
| h1 =>
  by 
    apply holds_nonneg_consts_core h1

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » dnf p)
theorem exists_clause_holds {v : Nat → Nat} {p : preform} :
  p.neg_free → p.sub_free → p.holds v → ∃ (c : _)(_ : c ∈ dnf p), clause.holds (fun x => ↑v x) c :=
  by 
    intro h1 h2 h3 
    rcases exists_clause_holds_core h1 h2 h3 with ⟨c, h4, h5⟩
    exists nonnegate c 
    have h6 : nonnegate c ∈ dnf p
    ·
      simp only [dnf]
      rw [List.mem_mapₓ]
      refine' ⟨c, h4, rfl⟩
    refine' ⟨h6, _⟩
    cases' c with eqs les 
    simp only [nonnegate, clause.holds]
    constructor 
    apply h5.left 
    rw [List.forall_mem_appendₓ]
    apply And.intro (holds_nonneg_consts _) h5.right 
    intro x 
    apply Int.coe_nat_nonneg

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (c «expr ∈ » dnf p)
theorem exists_clause_sat {p : preform} : p.neg_free → p.sub_free → p.sat → ∃ (c : _)(_ : c ∈ dnf p), clause.sat c :=
  by 
    intro h1 h2 h3 
    cases' h3 with v h3 
    rcases exists_clause_holds h1 h2 h3 with ⟨c, h4, h5⟩
    refine' ⟨c, h4, _, h5⟩

theorem unsat_of_unsat_dnf (p : preform) : p.neg_free → p.sub_free → clauses.unsat (dnf p) → p.unsat :=
  by 
    intro hnf hsf h1 h2 
    apply h1 
    apply exists_clause_sat hnf hsf h2

end Nat

end Omega

