/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/



import Std.Data.Rat.Basic
import Std.Data.Rat.Lemmas



namespace Smt



class Zero (α : Type u) where
  zero : α

namespace Zero
instance (priority := 300) toOfNat0 {α} [Zero α] : OfNat α 0 where
  ofNat := ‹Zero α›.1

instance (priority := 200) ofOfNat0 {α} [OfNat α 0] : Zero α where
  zero := 0
end Zero

section Zero
instance Nat.instZero : Zero Nat := ⟨0⟩

instance Int.instZero : Zero Int := ⟨0⟩

instance Rat.instZero : Zero Rat := ⟨0⟩
end Zero



class One (α : Type u) where
  one : α

namespace One
instance (priority := 300) toOfNat1 {α} [One α] : OfNat α 1 where
  ofNat := ‹One α›.1

instance (priority := 200) ofOfNat1 {α} [OfNat α 1] : One α where
  one := 1
end One

section One
instance Nat.instOne : One Nat := ⟨1⟩

instance Int.instOne : One Int := ⟨1⟩

instance Rat.instOne : One Rat := ⟨1⟩
end One



class NeZero [Zero α] (a : α) : Prop where
  out : a ≠ 0

section NeZero
instance Nat.instNeZeroSucc {n : Nat} : NeZero n.succ where
  out := Nat.succ_ne_zero n

instance Int.instNeZero_succ {n : Nat} : NeZero (↑n.succ : Int) where
  out := Int.ofNat_ne_zero.mpr <| Nat.succ_ne_zero n
instance Int.instNeZero_negSucc {n : Nat} : NeZero (Int.negSucc n) where
  out := Int.negSucc_ne_zero n

instance Rat.instNeZero {r : Rat} [NZNum : NeZero r.num] : NeZero r where
  out hz := by
    let h := NZNum.out
    rw [hz, Rat.num] at h
    contradiction
end NeZero



class ZeroLE {α : Type u} [Zero α] [LE α] (a : α) : Prop where
  out : 0 ≤ a

section lemmas
variable
  {α : Type u} {a : α}
  [Zero α] [LE α] [Self : ZeroLE a]

/-- `zero_le_one` with the type argument implicit. -/
@[simp]
theorem zero_le_one : (0 : α) ≤ a :=
  Self.out

variable (α)

/-- `zero_le_one` with the type argument explicit. -/
theorem zero_le_one' : (0 : α) ≤ a :=
  zero_le_one
end lemmas



section lemmas
variable [Zero α] [One α] [N : NeZero (1 : α)]

@[simp]
theorem one_ne_zero : (1 : α) ≠ 0 :=
  N.out

@[simp]
theorem zero_ne_one : (0 : α) ≠ 1 :=
  one_ne_zero.symm
end lemmas



/-- Class of types that have an inversion operation. -/
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

postfix:max "⁻¹" => Inv.inv



namespace Nat
variable [One α]

protected
def unaryCast [Zero α] [Add α] : Nat → α
| 0 => 0
| n + 1 => Nat.unaryCast n + 1

protected
def npowRec [Mul α] : Nat → α → α
| 0, _ => 1
| n + 1, a => Nat.npowRec n a * a
end Nat

namespace Int
protected
def castDef {α : Type u} [NatCast α] [Neg α] : Int → α
| (n : Nat) => n
| Int.negSucc n => -(n + 1 : Nat)
end Int



section Rat

/-- Nonnegative rational numbers. -/
def NNRat := {q : Rat // 0 ≤ q}

@[inherit_doc] notation "Rat≥0" => NNRat



/-- Typeclass for the canonical homomorphism `Rat≥0 → K`.

This should be considered as a notation typeclass. The sole purpose of this typeclass is to be
extended by `DivisionSemiring`. -/
class NNRatCast (α : Type u) where
  /-- The canonical homomorphism `Rat ≥ 0 → α`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : Rat≥0 → α

instance NNRat.instNNRatCast : NNRatCast Rat≥0 where
  nnratCast q := q

/-- Canonical homomorphism from `Rat≥0` to a division semiring `α`.

This is just the bare function in order to aid in creating instances of `DivisionSemiring`. -/
@[coe, reducible, match_pattern] protected
def NNRat.cast [NNRatCast α] : Rat≥0 → α := NNRatCast.nnratCast

-- See note [coercion into rings]
instance NNRatCast.toCoeTail [NNRatCast α] : CoeTail Rat≥0 α where
  coe := NNRat.cast

-- See note [coercion into rings]
instance NNRatCast.toCoeHTCT [NNRatCast α] : CoeHTCT Rat≥0 α where coe := NNRat.cast

instance Rat.instNNRatCast : NNRatCast Rat := ⟨Subtype.val⟩

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

/-- The numerator of a nonnegative rational. -/
def num (q : Rat≥0) : Nat := (q : Rat).num.natAbs

/-- The denominator of a nonnegative rational. -/
def den (q : Rat≥0) : Nat := (q : Rat).den

@[simp]
theorem num_mk (q : Rat) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
@[simp]
theorem den_mk (q : Rat) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl

@[norm_cast]
theorem cast_id (n : Rat≥0) : NNRat.cast n = n := rfl
@[simp]
theorem cast_eq_id : NNRat.cast = id := rfl

end NNRat



/-- Type class for the canonical homomorphism `Rat → K`. -/
class RatCast (K : Type u) where
  /-- The canonical homomorphism `Rat → K`. -/
  protected ratCast : Rat → K

namespace Rat

instance instRatCast : RatCast Rat where ratCast n := n

/-- Canonical homomorphism from `Rat` to a division ring `α`. This is just the bare function in
order to aid in creating instances of `DivisionRing`.
-/
@[coe, reducible, match_pattern] protected
def Rat.cast {α : Type u} [RatCast α] : Rat → α :=
  RatCast.ratCast

@[norm_cast]
theorem cast_id (n : Rat) : Rat.cast n = n := rfl
@[simp]
theorem cast_eq_id : Rat.cast = id := rfl

end Rat

end Rat
