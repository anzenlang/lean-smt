import Mathlib.Data.Real.Basic

import Smt.Util.Mathlib.Algebra
import Smt.Util.Mathlib.Covariant



namespace Smt



noncomputable instance instLinearOrderReal : LinearOrder Real where
  le_refl := Real.linearOrder.le_refl
  le_trans := Real.linearOrder.le_trans
  le_antisymm := Real.linearOrder.le_antisymm
  le_total := Real.linearOrder.le_total
  decidableLE := Real.linearOrder.decidableLE
  decidableLT := Real.linearOrder.decidableLT
  lt_iff_le_not_le := Real.linearOrder.lt_iff_le_not_le



instance instCovariantRealAddLT : CovariantClass Real Real (· + ·) (· < ·) where
  elim :=
    (Real.add_lt_add_iff_left · |>.mpr)
instance instCovariantRealSwapAddLT : CovariantClass Real Real (swap (· + ·)) (· < ·) where
  elim m := by
    simp
-- #TODO don't leverage mathlib instance
instance instCovariantRealAddLE : CovariantClass Real Real (· + ·) (· ≤ ·) where
  elim :=
    (inferInstance : _root_.CovariantClass Real Real (· + ·) (· ≤ ·)).elim
-- #TODO don't leverage mathlib instance
instance instCovariantRealSwapAddLE : CovariantClass Real Real (swap (· + ·)) (· ≤ ·) where
  elim :=
    (inferInstance : _root_.CovariantClass Real Real (swap (· + ·)) (· ≤ ·)).elim
