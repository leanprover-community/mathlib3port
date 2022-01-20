import Mathbin.Combinatorics.Quiver.Basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/


universe v v₁ v₂ u u₁ u₂

namespace Quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def hom.to_path {V} [Quiver V] {a b : V} (e : a ⟶ b) : path a b :=
  path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V]

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, path a b → ℕ
  | _, path.nil => 0
  | _, path.cons p _ => p.length + 1

instance {a : V} : Inhabited (path a a) :=
  ⟨path.nil⟩

@[simp]
theorem length_nil {a : V} : (path.nil : path a a).length = 0 :=
  rfl

@[simp]
theorem length_cons (a b c : V) (p : path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, path a b → path b c → path a c
  | _, p, path.nil => p
  | _, p, path.cons q e => (p.comp q).cons e

@[simp]
theorem comp_cons {a b c d : V} (p : path a b) (q : path b c) (e : c ⟶ d) : p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
theorem comp_nil {a b : V} (p : path a b) : p.comp path.nil = p :=
  rfl

@[simp]
theorem nil_comp {a : V} : ∀ {b} p : path a b, path.nil.comp p = p
  | a, path.nil => rfl
  | b, path.cons p e => by
    rw [comp_cons, nil_comp]

@[simp]
theorem comp_assoc {a b c : V} : ∀ {d} p : path a b q : path b c r : path c d, (p.comp q).comp r = p.comp (q.comp r)
  | c, p, q, path.nil => rfl
  | d, p, q, path.cons r e => by
    rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor V W)

/-- The image of a path under a prefunctor. -/
def map_path {a : V} : ∀ {b : V}, path a b → path (F.obj a) (F.obj b)
  | _, path.nil => path.nil
  | _, path.cons p e => path.cons (map_path p) (F.map e)

@[simp]
theorem map_path_nil (a : V) : F.map_path (path.nil : path a a) = path.nil :=
  rfl

@[simp]
theorem map_path_cons {a b c : V} (p : path a b) (e : b ⟶ c) :
    F.map_path (path.cons p e) = path.cons (F.map_path p) (F.map e) :=
  rfl

@[simp]
theorem map_path_comp {a b : V} (p : path a b) :
    ∀ {c : V} q : path b c, F.map_path (p.comp q) = (F.map_path p).comp (F.map_path q)
  | _, path.nil => rfl
  | _, path.cons p e => by
    dsimp
    rw [map_path_comp]

end Prefunctor

