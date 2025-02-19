/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- le_or_gt (x y : ℝ) : x ≤ y ∨ x > y

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra
  done


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · sorry
  done

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers
  done

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra
  done

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  sorry
  done

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  sorry
  done

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  sorry
  done

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  · numbers
  · constructor
    · numbers
    · constructor
      numbers
      numbers
  done

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry
  done

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry
  done

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry
  done

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry
  done

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry
  done

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry
  done

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry
  done

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry
  done

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
  done
