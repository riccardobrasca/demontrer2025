/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers
  done

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro hx
    have h : (x - 2) * (x + 3) = 0 := by
      calc
        (x - 2) * (x + 3) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw [hx]
    obtain h1 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
    · right
      addarith [h1]
    · left
      addarith [h2]
  · intro hx
    obtain hx | hx := hx
    · rw [hx]
      ring
    · rw [hx]
      ring
  done

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro ha
    have H : a ^ 2 - 5 * a + 6 = 0 := by
      apply le_antisymm
      · addarith [ha]
      · obtain Ha | Ha := le_or_succ_le a 2
        · calc
            a^2-5*a+6 = (a-2)^2-a+2 := by ring
            _ ≥ -a+2 := by extra
            _ ≥ -2+2 := by rel [Ha]
            _ ≥ 0 := by numbers
        · calc
            a^2-5*a+6 = (a-3)^2+a-3 := by ring
            _ ≥ (3-3)^2+3-3 := by rel [Ha]
            _ ≥ 0 := by numbers
    have H1 : (a - 2) * (a - 3) = 0 := by
      calc
        (a - 2) * (a - 3) = a ^ 2 - 5 * a + 6 := by ring
        _ = 0 := by rw [H]
    obtain H2 |H3 := eq_zero_or_eq_zero_of_mul_eq_zero H1
    · left
      addarith [H2]
    · right
      addarith [H3]
  · intro ha
    obtain ha | ha := ha
    · rw [ha]
      numbers
    · rw [ha]
      numbers
  done

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have H : 2*x = 2*6 := by addarith [h]
    cancel 2 at H
  · intro h
    rw [h]
    numbers
  done

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have H : k ^ 2 < 3 ^ 2 := by
      calc
        k ^ 2 ≤ 6 := by assumption
        _ < 3 ^ 2 := by numbers
    cancel 2 at H
    interval_cases k
    · left
      numbers
    · right
      left
      numbers
    · right
      right
      numbers
  · intro h
    obtain h | h | h := h
    · rw [h]
      numbers
    · rw [h]
      numbers
    · rw [h]
      numbers
  done
