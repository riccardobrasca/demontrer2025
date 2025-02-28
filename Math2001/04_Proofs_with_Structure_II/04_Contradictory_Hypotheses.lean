/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

-- mul_eq_zero {a b : ℝ} : a * b = 0 ↔ a = 0 ∨ b = 0
-- not_lt_of_ge {a b : ℝ} (h : a ≥ b) : ¬a < b

example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have H : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos
  done

example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H : (7 : ℤ) < 3 :=
    calc
      7 = t := by addarith [h]
      _ < 3 := h2
  have H1 : ¬(7 : ℤ) < 3 := by numbers
  contradiction
  done

example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H : (7 : ℤ) < 3 :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!
  done

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  sorry
  done

/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  sorry
  done

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : (x + 2) * (x - 2) = 0 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  sorry
  done
