/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- mul_eq_zero {a b : ℝ} : a * b = 0 ↔ a = 0 ∨ b = 0
-- not_lt_of_ge {a b : ℝ} (h : a ≥ b) : ¬a < b

example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  have hx3 : x ≠ 1 := by
    rw [hx2]
    numbers
  contradiction
  done


example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  rw [hx1] at hx2
  numbers at hx2
  done

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
  have Ha3 := le_or_succ_le a 2
  obtain Ha3 | Ha3 := Ha3
  · interval_cases a
    · have Hb1 := le_or_succ_le b 1
      obtain Hb1 | Hb1 := Hb1
      · interval_cases b
        have H : 1^2+1^2 ≠ c ^ 2 := by
          have Hc1 := le_or_succ_le c 1
          obtain Hc1 | Hc1 := Hc1
          · interval_cases c
            numbers
          · apply ne_of_lt
            calc
              c^2 ≥ 2 ^ 2 :=  by rel [Hc1]
              _ > 1^2+1^2 := by numbers
        contradiction
      · have Hbc := lt_trichotomy b c
        have H : ¬(1^2+b^2=c^2) := by
          obtain Hbc | Hbc | Hbc := Hbc
          · have Hbc' : c ≥ b + 1 := by
              addarith [Hbc]
            apply ne_of_lt
            calc
              c^2 ≥ (b+1) ^ 2 := by rel [Hbc']
              _ = 1^2 + b^2 + 2*b := by ring
              _ > 1^2 + b^2 := by extra
          · rw [Hbc]
            apply ne_of_gt
            extra
          · apply ne_of_gt
            calc
              c^2 < b^2 := by rel [Hbc]
              _ < 1^2+b^2 := by extra
        contradiction
    · have Hb1 := le_or_succ_le b 1
      obtain Hb1 | Hb1 := Hb1
      · interval_cases b
        have Hc : c < 3 := by
          have Hc' : c ^ 2 < 3 ^ 2 := by
            calc
              c^2 = 2^2+1^2 := by rw [h]
              _ < 3^2 := by numbers
          cancel 2 at Hc'
        interval_cases c
        · numbers at h
        · numbers at h
      · have Hbc := lt_trichotomy b c
        have H : ¬(2^2+b^2=c^2) := by
          obtain Hbc | Hbc | Hbc := Hbc
          · have Hbc' : c ≥ b + 1 := by
              addarith [Hbc]
            apply ne_of_lt
            calc
              c^2 ≥ (b+1)^2 := by rel [Hbc']
              _ = 2*b + (b^2+1) := by ring
              _ ≥ 2*2 + (b^2+1) := by rel [Hb1]
              _ > 2^2+b^2 := by extra
          · rw [Hbc]
            apply ne_of_gt
            extra
          · apply ne_of_gt
            calc
              c^2 < b^2 := by rel [Hbc]
              _ < 2^2+b^2 := by extra
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
