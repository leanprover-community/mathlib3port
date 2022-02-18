import Mathbin.SetTheory.OrdinalArithmetic

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Todo
* Prove the characterization of additive principal ordinals.
* Prove the characterization of multiplicative principal ordinals.
* Refactor any related theorems from `ordinal_arithmetic` into this file.
-/


universe u

noncomputable section

namespace Ordinal

/-! ### Principal ordinals -/


/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_iff_principal_swap {op : Ordinal → Ordinal → Ordinal} {o : Ordinal} :
    Principal op o ↔ Principal (Function.swap op) o := by
  constructor <;> exact fun h a b ha hb => h hb ha

theorem principal_zero {op : Ordinal → Ordinal → Ordinal} : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim

@[simp]
theorem principal_one_iff {op : Ordinal → Ordinal → Ordinal} : Principal op 1 ↔ op 0 0 = 0 := by
  refine' ⟨fun h => _, fun h a b ha hb => _⟩
  · rwa [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
    
  · rwa [lt_one_iff_zero, ha, hb] at *
    

theorem principal.iterate_lt {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o)
    (n : ℕ) : (op a^[n]) a < o := by
  induction' n with n hn
  · rwa [Function.iterate_zero]
    
  · rw [Function.iterate_succ']
    exact ho hao hn
    

theorem op_eq_self_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal.{u}} (hao : a < o)
    (H : IsNormal (op a)) (ho : Principal op o) (ho' : IsLimit o) : op a o = o := by
  refine' le_antisymmₓ _ (H.self_le _)
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le]
  exact fun b hbo => le_of_ltₓ (ho hao hbo)

theorem nfp_le_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o) :
    nfp (op a) a ≤ o :=
  nfp_le.2 fun n => le_of_ltₓ (ho.iterate_lt hao n)

/-! ### Principal ordinals are unbounded -/


/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  lsub fun x : o.out.α × o.out.α => op (typein o.out.R x.1) (typein o.out.R x.2)

theorem lt_blsub₂ (op : Ordinal → Ordinal → Ordinal) {o : Ordinal} {a b : Ordinal} (ha : a < o) (hb : b < o) :
    op a b < blsub₂ op o := by
  convert
    lt_lsub _
      (Prod.mk
        (enum o.out.r a
          (by
            rwa [type_out]))
        (enum o.out.r b
          (by
            rwa [type_out])))
  simp only [typein_enum]

theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (blsub₂.{u, u} op) o) := by
  intro a b ha hb
  rw [lt_nfp] at *
  cases' ha with m hm
  cases' hb with n hn
  cases' le_totalₓ ((blsub₂.{u, u} op^[m]) o) ((blsub₂.{u, u} op^[n]) o) with h h
  · use n + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op (hm.trans_le h) hn
    
  · use m + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op hm (hn.trans_le h)
    

theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) : Set.Unbounded (· < ·) { o | Principal op o } :=
  fun o => ⟨_, principal_nfp_blsub₂ op o, (le_nfp_self _ o).not_lt⟩

end Ordinal

