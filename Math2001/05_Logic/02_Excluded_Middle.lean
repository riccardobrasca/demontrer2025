/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction
  done

/-! # Exercises -/

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h hQ
    by_cases hP : P
    · assumption
    · have hnotQ : ¬Q := by
        apply h
        assumption
      contradiction
  · intro h hnotP
    by_contra' hQ
    have hP : P := by
      apply h
      assumption
    contradiction
  done
