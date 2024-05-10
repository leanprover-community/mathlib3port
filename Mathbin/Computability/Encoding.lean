/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Data.Fintype.Basic
import Data.Num.Lemmas
import SetTheory.Cardinal.Ordinal
import Tactic.DeriveFintype

#align_import computability.encoding from "leanprover-community/mathlib"@"814d76e2247d5ba8bc024843552da1278bfe9e5c"

/-!
# Encodings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/


universe u v

open scoped Cardinal

namespace Computability

#print Computability.Encoding /-
/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure Encoding (α : Type u) where
  Γ : Type v
  encode : α → List Γ
  decode : List Γ → Option α
  decode_encode : ∀ x, decode (encode x) = some x
#align computability.encoding Computability.Encoding
-/

#print Computability.Encoding.encode_injective /-
theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode :=
  by
  refine' fun _ _ h => Option.some_injective _ _
  rw [← e.decode_encode, ← e.decode_encode, h]
#align computability.encoding.encode_injective Computability.Encoding.encode_injective
-/

#print Computability.FinEncoding /-
/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  ΓFin : Fintype Γ
#align computability.fin_encoding Computability.FinEncoding
-/

instance {α : Type u} (e : FinEncoding α) : Fintype e.toEncoding.Γ :=
  e.ΓFin

#print Computability.Γ' /-
/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype
#align computability.Γ' Computability.Γ'
-/

#print Computability.inhabitedΓ' /-
instance inhabitedΓ' : Inhabited Γ' :=
  ⟨Γ'.blank⟩
#align computability.inhabited_Γ' Computability.inhabitedΓ'
-/

#print Computability.inclusionBoolΓ' /-
/-- The natural inclusion of bool in Γ'. -/
def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit
#align computability.inclusion_bool_Γ' Computability.inclusionBoolΓ'
-/

#print Computability.sectionΓ'Bool /-
/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default Bool
#align computability.section_Γ'_bool Computability.sectionΓ'Bool
-/

#print Computability.leftInverse_section_inclusion /-
theorem leftInverse_section_inclusion : Function.LeftInverse sectionΓ'Bool inclusionBoolΓ' :=
  fun x => Bool.casesOn x rfl rfl
#align computability.left_inverse_section_inclusion Computability.leftInverse_section_inclusion
-/

#print Computability.inclusionBoolΓ'_injective /-
theorem inclusionBoolΓ'_injective : Function.Injective inclusionBoolΓ' :=
  Function.HasLeftInverse.injective (Exists.intro sectionΓ'Bool leftInverse_section_inclusion)
#align computability.inclusion_bool_Γ'_injective Computability.inclusionBoolΓ'_injective
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Computability.encodePosNum /-
/-- An encoding function of the positive binary numbers in bool. -/
def encodePosNum : PosNum → List Bool
  | PosNum.one => [true]
  | PosNum.bit0 n => false::encode_pos_num n
  | PosNum.bit1 n => true::encode_pos_num n
#align computability.encode_pos_num Computability.encodePosNum
-/

#print Computability.encodeNum /-
/-- An encoding function of the binary numbers in bool. -/
def encodeNum : Num → List Bool
  | Num.zero => []
  | Num.pos n => encodePosNum n
#align computability.encode_num Computability.encodeNum
-/

#print Computability.encodeNat /-
/-- An encoding function of ℕ in bool. -/
def encodeNat (n : ℕ) : List Bool :=
  encodeNum n
#align computability.encode_nat Computability.encodeNat
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Computability.decodePosNum /-
/-- A decoding function from `list bool` to the positive binary numbers. -/
def decodePosNum : List Bool → PosNum
  | ff::l => PosNum.bit0 (decode_pos_num l)
  | tt::l => ite (l = []) PosNum.one (PosNum.bit1 (decode_pos_num l))
  | _ => PosNum.one
#align computability.decode_pos_num Computability.decodePosNum
-/

#print Computability.decodeNum /-
/-- A decoding function from `list bool` to the binary numbers. -/
def decodeNum : List Bool → Num := fun l => ite (l = []) Num.zero <| decodePosNum l
#align computability.decode_num Computability.decodeNum
-/

#print Computability.decodeNat /-
/-- A decoding function from `list bool` to ℕ. -/
def decodeNat : List Bool → Nat := fun l => decodeNum l
#align computability.decode_nat Computability.decodeNat
-/

#print Computability.encodePosNum_nonempty /-
theorem encodePosNum_nonempty (n : PosNum) : encodePosNum n ≠ [] :=
  PosNum.casesOn n (List.cons_ne_nil _ _) (fun m => List.cons_ne_nil _ _) fun m =>
    List.cons_ne_nil _ _
#align computability.encode_pos_num_nonempty Computability.encodePosNum_nonempty
-/

#print Computability.decode_encodePosNum /-
theorem decode_encodePosNum : ∀ n, decodePosNum (encodePosNum n) = n :=
  by
  intro n
  induction' n with m hm m hm <;> unfold encode_pos_num decode_pos_num
  · rfl
  · rw [hm]
    exact if_neg (encode_pos_num_nonempty m)
  · exact congr_arg PosNum.bit0 hm
#align computability.decode_encode_pos_num Computability.decode_encodePosNum
-/

#print Computability.decode_encodeNum /-
theorem decode_encodeNum : ∀ n, decodeNum (encodeNum n) = n :=
  by
  intro n
  cases n <;> unfold encode_num decode_num
  · rfl
  rw [decode_encode_pos_num n]
  rw [PosNum.cast_to_num]
  exact if_neg (encode_pos_num_nonempty n)
#align computability.decode_encode_num Computability.decode_encodeNum
-/

#print Computability.decode_encodeNat /-
theorem decode_encodeNat : ∀ n, decodeNat (encodeNat n) = n :=
  by
  intro n
  conv_rhs => rw [← Num.to_of_nat n]
  exact congr_arg coe (decode_encode_num ↑n)
#align computability.decode_encode_nat Computability.decode_encodeNat
-/

#print Computability.encodingNatBool /-
/-- A binary encoding of ℕ in bool. -/
def encodingNatBool : Encoding ℕ where
  Γ := Bool
  encode := encodeNat
  decode n := some (decodeNat n)
  decode_encode n := congr_arg _ (decode_encodeNat n)
#align computability.encoding_nat_bool Computability.encodingNatBool
-/

#print Computability.finEncodingNatBool /-
/-- A binary fin_encoding of ℕ in bool. -/
def finEncodingNatBool : FinEncoding ℕ :=
  ⟨encodingNatBool, Bool.fintype⟩
#align computability.fin_encoding_nat_bool Computability.finEncodingNatBool
-/

#print Computability.encodingNatΓ' /-
/-- A binary encoding of ℕ in Γ'. -/
def encodingNatΓ' : Encoding ℕ where
  Γ := Γ'
  encode x := List.map inclusionBoolΓ' (encodeNat x)
  decode x := some (decodeNat (List.map sectionΓ'Bool x))
  decode_encode x :=
    congr_arg _ <| by
      rw [List.map_map, List.map_id'' left_inverse_section_inclusion, decode_encode_nat]
#align computability.encoding_nat_Γ' Computability.encodingNatΓ'
-/

#print Computability.finEncodingNatΓ' /-
/-- A binary fin_encoding of ℕ in Γ'. -/
def finEncodingNatΓ' : FinEncoding ℕ :=
  ⟨encodingNatΓ', Γ'.fintype⟩
#align computability.fin_encoding_nat_Γ' Computability.finEncodingNatΓ'
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Computability.unaryEncodeNat /-
/-- A unary encoding function of ℕ in bool. -/
def unaryEncodeNat : Nat → List Bool
  | 0 => []
  | n + 1 => true::unary_encode_nat n
#align computability.unary_encode_nat Computability.unaryEncodeNat
-/

#print Computability.unaryDecodeNat /-
/-- A unary decoding function from `list bool` to ℕ. -/
def unaryDecodeNat : List Bool → Nat :=
  List.length
#align computability.unary_decode_nat Computability.unaryDecodeNat
-/

#print Computability.unary_decode_encode_nat /-
theorem unary_decode_encode_nat : ∀ n, unaryDecodeNat (unaryEncodeNat n) = n := fun n =>
  Nat.rec rfl (fun (m : ℕ) hm => (congr_arg Nat.succ hm.symm).symm) n
#align computability.unary_decode_encode_nat Computability.unary_decode_encode_nat
-/

#print Computability.unaryFinEncodingNat /-
/-- A unary fin_encoding of ℕ. -/
def unaryFinEncodingNat : FinEncoding ℕ where
  Γ := Bool
  encode := unaryEncodeNat
  decode n := some (unaryDecodeNat n)
  decode_encode n := congr_arg _ (unary_decode_encode_nat n)
  ΓFin := Bool.fintype
#align computability.unary_fin_encoding_nat Computability.unaryFinEncodingNat
-/

#print Computability.encodeBool /-
/-- An encoding function of bool in bool. -/
def encodeBool : Bool → List Bool :=
  List.pure
#align computability.encode_bool Computability.encodeBool
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Computability.decodeBool /-
/-- A decoding function from `list bool` to bool. -/
def decodeBool : List Bool → Bool
  | b::_ => b
  | _ => Inhabited.default Bool
#align computability.decode_bool Computability.decodeBool
-/

#print Computability.decode_encodeBool /-
theorem decode_encodeBool : ∀ b, decodeBool (encodeBool b) = b := fun b => Bool.casesOn b rfl rfl
#align computability.decode_encode_bool Computability.decode_encodeBool
-/

#print Computability.finEncodingBoolBool /-
/-- A fin_encoding of bool in bool. -/
def finEncodingBoolBool : FinEncoding Bool
    where
  Γ := Bool
  encode := encodeBool
  decode x := some (decodeBool x)
  decode_encode x := congr_arg _ (decode_encodeBool x)
  ΓFin := Bool.fintype
#align computability.fin_encoding_bool_bool Computability.finEncodingBoolBool
-/

#print Computability.inhabitedFinEncoding /-
instance inhabitedFinEncoding : Inhabited (FinEncoding Bool) :=
  ⟨finEncodingBoolBool⟩
#align computability.inhabited_fin_encoding Computability.inhabitedFinEncoding
-/

#print Computability.inhabitedEncoding /-
instance inhabitedEncoding : Inhabited (Encoding Bool) :=
  ⟨finEncodingBoolBool.toEncoding⟩
#align computability.inhabited_encoding Computability.inhabitedEncoding
-/

#print Computability.Encoding.card_le_card_list /-
theorem Encoding.card_le_card_list {α : Type u} (e : Encoding.{u, v} α) :
    Cardinal.lift.{v} (#α) ≤ Cardinal.lift.{u} (#List e.Γ) :=
  Cardinal.lift_mk_le'.2 ⟨⟨e.encode, e.encode_injective⟩⟩
#align computability.encoding.card_le_card_list Computability.Encoding.card_le_card_list
-/

#print Computability.Encoding.card_le_aleph0 /-
theorem Encoding.card_le_aleph0 {α : Type u} (e : Encoding.{u, v} α) [Encodable e.Γ] : (#α) ≤ ℵ₀ :=
  by
  refine' Cardinal.lift_le.1 (e.card_le_card_list.trans _)
  simp only [Cardinal.lift_aleph0, Cardinal.lift_le_aleph0]
  cases' isEmpty_or_nonempty e.Γ with h h
  · simp only [Cardinal.mk_le_aleph0]
  · rw [Cardinal.mk_list_eq_aleph0]
#align computability.encoding.card_le_aleph_0 Computability.Encoding.card_le_aleph0
-/

#print Computability.FinEncoding.card_le_aleph0 /-
theorem FinEncoding.card_le_aleph0 {α : Type u} (e : FinEncoding α) : (#α) ≤ ℵ₀ :=
  haveI : Encodable e.Γ := Fintype.toEncodable _
  e.to_encoding.card_le_aleph_0
#align computability.fin_encoding.card_le_aleph_0 Computability.FinEncoding.card_le_aleph0
-/

end Computability

