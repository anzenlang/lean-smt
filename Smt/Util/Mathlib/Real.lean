import Mathlib.Data.Real.Basic

import Smt.Util.Mathlib.Algebra



namespace Smt



noncomputable instance instLinearOrderReal : LinearOrder Real where
  le_refl := Real.linearOrder.le_refl
  le_trans := Real.linearOrder.le_trans
  le_antisymm := Real.linearOrder.le_antisymm
  le_total := Real.linearOrder.le_total
  decidableLE := Real.linearOrder.decidableLE
  decidableLT := Real.linearOrder.decidableLT
  lt_iff_le_not_le := Real.linearOrder.lt_iff_le_not_le
