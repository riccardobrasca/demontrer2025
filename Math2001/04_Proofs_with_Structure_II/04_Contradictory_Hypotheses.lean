/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

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
  obtain H1 | H1 := le_or_succ_le a 2
  · obtain H2 | H2 := le_or_succ_le b 1
    · have H3 : c^2 < 3^2 := by
        calc
          c^2 ≤ a^2 + b^2 := by addarith [h]
          _ ≤ 2^2 + 1^2 := by rel [H1, H2]
          _ < 3^2 := by numbers
      cancel 2 at H3
      interval_cases b
      interval_cases c
      · interval_cases a
        · numbers at h
        · numbers at h
      · interval_cases a
        · numbers at h
        · numbers at h
    · have H : b^2 < c^2 := by
        calc
          b^2 = b^2 + 0^2 := by ring
          _ < b^2 + a^2 := by rel [ha]
          _ = a^2 + b^2 := by ring
          _ = c^2 := by rw [h]
      cancel 2 at H
      have H3 : c^2 < (b+1)^2 := by
        calc
          c^2 = a^2 + b^2 := by rw [h]
          _ ≤ 2^2+b^2 := by rel [H1]
          _ = b^2 + 2*2 := by ring
          _ ≤ b^2 + 2*b := by rel [H2]
          _ < b^2 + 2*b+1 := by extra
          _ = (b+1)^2 := by ring
      cancel 2 at H3
      have H4 : ¬(c < b+1) := by
        apply not_lt_of_ge
        addarith [H]
      contradiction
  · assumption
  done

/-! # Exercises -/

-- note that `cancel n at h` works immediately, but this is just because it uses `le_of_pow_le_pow`
-- that is essentially this exercise. If someone does it, let's check they understand the math
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  obtain H | H := le_or_gt y x
  · assumption
  · have hy : 0 ≤ y := by
      calc
        y ≥  x := by addarith [H]
        _ ≥ 0 := hx
    cancel n at h
  done

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : (x + 2) * (x - 2) = 0 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h4 | h5 := h3
  · have h6 : x = - 2 := by addarith [h4]
    rw [h6] at h2
    numbers at h2
  · addarith [h5]
  done
