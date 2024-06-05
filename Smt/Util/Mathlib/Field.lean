/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/



import Smt.Util.Mathlib.Group.Extra



namespace Smt



def DivInvMonoid.div' {α : Type u} [Monoid α] [Inv α] (a b : α) : α := a * b⁻¹

class DivInvMonoid (α : Type u) extends Monoid α, Inv α, Div α where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : Int → α → α := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : α, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : Nat) (a : α) : zpow (Int.ofNat n.succ) a = zpow (Int.ofNat n) a  * a :=
    by intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : Nat) (a : α) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ :=
    by intros; rfl

class DivisionRing (α : Type u)
  extends Ring α, DivInvMonoid α, Nontrivial α, NNRatCast α, RatCast α where
  /-- For a nonzero `a`, `a⁻¹` is a right multiplicative inverse. -/
  protected mul_inv_cancel : ∀ (a : α), a ≠ 0 → a * a⁻¹ = 1
  /-- The inverse of `0` is `0` by convention. -/
  protected inv_zero : (0 : α)⁻¹ = 0
  protected nnratCast := NNRat.castRec
  /-- However `NNRat.cast` is defined, it must be equal to `a / b`.

  Do not use this lemma directly. Use `NNRat.cast_def` instead. -/
  protected nnratCast_def (q : Rat≥0) : (NNRat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a nonnegative rational number.

  Unless there is a risk of a `Module Rat≥0 _` instance diamond, write `nnqsmul := _`. This will set
  `nnqsmul` to `(NNRat.cast · * ·)` thanks to unification in the default proof of `nnqsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected nnqsmul : Rat≥0 → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `NNRat.smul_def` instead. -/
  protected nnqsmul_def (q : Rat≥0) (a : α) : nnqsmul q a = NNRat.cast q * a := by intros; rfl
  protected ratCast := Rat.castRec
  /-- However `Rat.cast q` is defined, it must be propositionally equal to `q.num / q.den`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected ratCast_def (q : Rat) : (Rat.cast q : α) = q.num / q.den := by intros; rfl
  /-- Scalar multiplication by a rational number.

  Unless there is a risk of a `Module Rat _` instance diamond, write `qsmul := _`. This will set
  `qsmul` to `(Rat.cast · * ·)` thanks to unification in the default proof of `qsmul_def`.

  Do not use directly. Instead use the `•` notation. -/
  protected qsmul : Rat → α → α
  /-- However `qsmul` is defined, it must be propositionally equal to multiplication by `Rat.cast`.

  Do not use this lemma directly. Use `Rat.cast_def` instead. -/
  protected qsmul_def (a : Rat) (x : α) : qsmul a x = Rat.cast a * x := by intros; rfl

class Field (α : Type u) extends CommRing α, DivisionRing α

class LinearOrderedField (α : Type u) extends LinearOrderedCommRing α, Field α
