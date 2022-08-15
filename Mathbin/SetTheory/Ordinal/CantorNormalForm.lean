/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open Order

namespace Ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elabAsElim]
noncomputable def cNFRec (b : Ordinal) {C : Ordinal → Sort _} (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    ∀ o, C o
  | o =>
    if ho : o = 0 then by
      rwa [ho]
    else
      let hwf := mod_opow_log_lt_self b ho
      H o ho (CNF_rec (o % b ^ log b o))

@[simp]
theorem CNF_rec_zero {C : Ordinal → Sort _} (b : Ordinal) (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    @cNFRec b C H0 H 0 = H0 := by
  rw [CNF_rec, dif_pos rfl]
  rfl

theorem CNF_rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort _} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : @cNFRec b C H0 H o = H o ho (@cNFRec b C H0 H _) := by
  rw [CNF_rec, dif_neg ho]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def cNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  cNFRec b [] (fun o ho IH => (log b o, o / b ^ log b o) :: IH) o

@[simp]
theorem CNF_zero (b : Ordinal) : cNF b 0 = [] :=
  CNF_rec_zero b _ _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) : cNF b o = (log b o, o / b ^ log b o) :: cNF b (o % b ^ log b o) :=
  CNF_rec_pos b ho _ _

theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : cNF 0 o = [⟨0, o⟩] := by
  simp [← CNF_ne_zero ho]

theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : cNF 1 o = [⟨0, o⟩] := by
  simp [← CNF_ne_zero ho]

theorem CNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : cNF b o = [⟨0, o⟩] := by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
    
  · exact one_CNF ho
    

theorem CNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : cNF b o = [⟨0, o⟩] := by
  simp [← CNF_ne_zero ho, ← log_eq_zero hb]

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (cNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  cNFRec b
    (by
      rw [CNF_zero]
      rfl)
    (fun o ho IH => by
      rw [CNF_ne_zero ho, List.foldr_cons, IH, div_add_mod])
    o

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ cNF b o → x.1 ≤ log b o := by
  refine' CNF_rec b _ (fun o ho H => _) o
  · rw [CNF_zero]
    exact False.elim
    
  · rw [CNF_ne_zero ho, List.mem_cons_iffₓ]
    rintro (rfl | h)
    · exact le_rfl
      
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)
      
    

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ cNF b o) : x.1 ≤ o :=
  (CNF_fst_le_log h).trans <| log_le_self _ _

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ cNF b o → 0 < x.2 := by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
    
  · rcases eq_zero_or_pos b with (rfl | hb)
    · rw [zero_CNF ho, List.mem_singletonₓ]
      rintro rfl
      exact Ordinal.pos_iff_ne_zero.2 ho
      
    · rw [CNF_ne_zero ho]
      rintro (rfl | h)
      · simp
        rw [div_pos]
        · exact opow_log_le_self _ ho
          
        · exact (opow_pos _ hb).ne'
          
        
      · exact IH h
        
      
    

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} : x ∈ cNF b o → x.2 < b := by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
    
  · rw [CNF_ne_zero ho]
    rintro (rfl | h)
    · simpa using div_opow_log_lt o hb
      
    · exact IH h
      
    

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : Ordinal) : ((cNF b o).map Prod.fst).Sorted (· > ·) := by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
    
  · cases' le_or_ltₓ b 1 with hb hb
    · simp [← CNF_of_le_one hb ho]
      
    · cases' lt_or_leₓ o b with hob hbo
      · simp [← CNF_of_lt ho hob]
        
      · rw [CNF_ne_zero ho, List.map_cons, List.sorted_cons]
        refine' ⟨fun a H => _, IH⟩
        rw [List.mem_mapₓ] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb ho hbo)
        
      
    

end Ordinal

