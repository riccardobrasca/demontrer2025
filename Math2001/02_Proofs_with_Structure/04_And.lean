/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring
  done


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3 := by
    apply abs_le_of_sq_le_sq'
    · calc
        p ^ 2 ≤ 9 := by addarith [hp]
        _ = 3 ^ 2 := by numbers
    · numbers
  obtain ⟨h1, h2⟩ := hp'
  calc
    p ≥ -3 := h1
    _ ≥ -5 := by numbers
  done

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]
  done

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb
  done

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0 := by
    apply le_antisymm
    · calc
        a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
    · extra
  have h3 : b ^ 2 = 0 := by
    apply le_antisymm
    · calc
        b ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
        _ = 0 := by rw [h1]
    · extra
  constructor
  · cancel 2 at h2
  · cancel 2 at h3
  done

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h1, h2]
    _ = 4 := by numbers
  done

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2*r = (r+s)+(r-s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by numbers
  done

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  have h3 : m + 5 ≤ 8 :=
    calc
      m + 5 ≤ n := h2
      _ ≤ 8 := h1
  addarith [h3]
  done

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h : p ≥ 7 := by addarith [hp]
  constructor
  · calc
      p ^ 2 ≥ 7^2 := by rel [h]
      _ = 49 := by numbers
  · addarith [h]
  done

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have ha : a ≥ 6 := by addarith [h]
  constructor
  · addarith [ha]
  · calc
      3*a ≥ 3*6 := by rel [ha]
      _ ≥ 10 := by numbers
  done

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · calc
      x = 2*(x + y) - (x + 2*y) := by ring
      _ = 2*5 - 7 := by rw [h1, h2]
      _ = 3 := by numbers
  · calc
      y = (x+2*y)-(x+y) := by ring
      _ = 7 - 5 := by rw [h1, h2]
      _ = 2 := by numbers
  done

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : a*(b-1) = 0 := by
    calc
      a*(b-1) = a*b - a := by ring
      _ = a - a := by rw [h1]
      _ = 0 := by ring
  have h4 : b*(a-1) = 0 := by
    calc
      b*(a-1) = a*b - b := by ring
      _ = b - b := by rw [h2]
      _ = 0 := by ring
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  have h6 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  obtain h5 | h5 := h5
  · obtain h6 | h6 := h6
    · left
      constructor
      · assumption
      · assumption
    · have h7 : a ≠ 0 := by addarith [h6]
      contradiction
  · obtain h6 | h6 := h6
    · have h7 : b ≠ 0 := by addarith [h5]
      contradiction
    · right
      constructor
      · addarith [h6]
      · addarith [h5]
  done
