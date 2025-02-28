/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b

example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 := by
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers
  done


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain h1 | h2 := h ((a+b)/2)
  · calc
      a = 2*a-a := by ring
      _ ≤ 2*((a+b)/2)-a := by rel [h1]
      _ = b := by ring
  · calc
      a = 2*((a+b)/2)-b := by ring
      _ ≤ 2*b-b := by rel [h2]
      _ = b := by ring
  done

example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) : a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1
  done

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring
  done

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have hxy : (x+y)^2 ≤ 3^2 := by
    calc
      (x+y)^2 ≤ (x+y)^2 + (x-y)^2  := by extra
      _ = 2*(x^2+y^2) := by ring
      _ ≤ 2*4 := by rel [h]
      _ ≤ 3^2 := by numbers
  have H := abs_le_of_sq_le_sq' hxy (by numbers)
  obtain ⟨H1, H2⟩ := H
  addarith [H1]
  done

example : ∃ (k : ℤ), ∀ n ≥ k, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  use 5
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra
  done

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  sorry
  done

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry
  done

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry
  done

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry
  done

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry
  done

example : ¬(Prime 45) := by
  sorry
  done
