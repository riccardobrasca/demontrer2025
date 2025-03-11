/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Mathlib.Tactic.ByContra

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  by_contra' h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this
  done

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  by_contra' h
  obtain ⟨hx, hy⟩ := h
  have H : (0 : ℝ) > 0 :=
    calc
      0 = x + y := by rw [h]
      _ > 0 := by extra
  numbers at H
  done

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry
  done

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry
  done

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry
  done

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry
  done
