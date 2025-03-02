/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction
  done

/-! # Exercises -/

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  sorry
  done
