/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]
  done

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    2 < 2 ^ 2 := by numbers
    _ ≤ n ^ 2 := by rel [hn]
  done

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers
  done


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  left
  addarith [h2]
  right
  addarith [h2]
  done

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]
  done


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h | h := h
  calc
    x ^ 2 + 1 = 4 ^ 2 + 1 := by rw [h]
    _ = 17 := by numbers
  calc
    x ^ 2 + 1 = (-4) ^ 2 + 1 := by rw [h]
    _ = 17 := by numbers
  done

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  calc
    x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [h]
    _ = 0 := by numbers
  calc
    x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [h]
    _ = 0 := by numbers
  done

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  calc
    t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h]
    _ = 0 := by numbers
  calc
    t ^ 2 - t - 6 = 3 ^ 2 - 3 - 6 := by rw [h]
    _ = 0 := by numbers
  done

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h | h := h
  calc
    x * y + 2 * x = 2 * y + 2 * 2 := by rw [h]
    _ = 2 * y + 4 := by ring
  calc
    x * y + 2 * x = x * (-2) + 2 * x := by rw [h]
    _ = 2*(-2) + 4 := by ring
    _ = 2 * y + 4 := by rw [h]
  done

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith [h]
  done

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith [h]
  done

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have h1 : y-1 < y - 0 := by extra
  left
  calc
    x = (2*x+1-1)/2 := by ring
    _ = (y-1)/2 := by rw [h]
    _ < (y - 0)/2 := by rel [h1]
    _ = y/2 := by ring
  done

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : (x + 3) * (x - 1) = 0 := by
    calc
      (x + 3) * (x - 1) = x ^ 2 + 2*x - 3 := by ring
      _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | h2 := h2
  left
  addarith [h2]
  right
  addarith [h2]
  done

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : a ^ 2 + 2 * b ^ 2 - 3 * a * b = 0 := by addarith [hab]
  have h2 : (a-b)*(a-2*b)=0 := by
    calc
      (a-b)*(a-2*b) = a^2 + 2*b^2 - 3*a*b := by ring
      _ = 0 := by rw [h1]
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain h3 | h3 := h3
  left
  addarith [h3]
  right
  addarith [h3]
  done

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : t^3-t^2 = 0 := by addarith [ht]
  have h2 : t * (t^2 - t) = 0 := by
    calc
      t * (t^2 - t) = t^3 - t^2 := by ring
      _ = 0 := by rw [h1]
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain h3 | h3 := h3
  right
  addarith [h3]
  have h4 : t * (t - 1) = 0 := by
    calc
      t * (t - 1) = t^2 - t := by ring
      _ = 0 := by rw [h3]
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  obtain h5 | h5 := h5
  right
  addarith [h5]
  left
  addarith [h5]
  done

example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 2 ^ 2 := by rel [hn]
      _ < 7 := by numbers
  · apply ne_of_gt
    calc
      7 < 3 ^ 2 := by numbers
      _ ≤ n ^ 2 := by rel [hn]
  done

example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hx | hx := hx
  · apply ne_of_lt
    calc
      2 * x ≤ 2 * 1 := by rel [hx]
      _ < 3 := by numbers
  · apply ne_of_gt
    calc
      3 < 2 * 2 := by numbers
      _ ≤ 2 * x := by rel [hx]
  done

example {t : ℤ} : 5 * t ≠ 18 := by
  have ht := le_or_succ_le t 3
  obtain ht | ht := ht
  · apply ne_of_lt
    calc
      5 * t ≤ 5 * 3 := by rel [ht]
      _ < 18 := by numbers
  · apply ne_of_gt
    calc
      18 < 5 * 4 := by numbers
      _ ≤ 5 * t := by rel [ht]
  done

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hm | hm := hm
  · apply ne_of_lt
    calc
      m ^ 2 + 4 * m ≤ 5 ^ 2 + 4 * 5 := by rel [hm]
      _ < 46 := by numbers
  · apply ne_of_gt
    calc
      46 < 6 ^ 2 + 4 * 6 := by numbers
      _ ≤ m ^ 2 + 4 * m := by rel [hm]
  done
