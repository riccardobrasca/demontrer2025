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
  obtain ⟨h1,h2⟩ := hp'
  addarith [h1]
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
  obtain ⟨h1,h2⟩ := H
  calc 2*a+b = a +(a+b) := by ring
    _ ≤ 1+3 := by rel[h1,h2]
    _ = 4 := by numbers
  done
  done


example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1,h2⟩ := H
  calc 2*r = (r+s) + (r-s) := by ring
    _ ≤ 1+5 := by rel[h1,h2]
    _ = 6 := by numbers
  done
  done


example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1,h2⟩ := H
  calc m = (m+5)-5 := by ring
    _ ≤ n - 5 := by rel[h2]
    _ ≤ 8-5 := by rel[h1]
    _ = 3 := by numbers
  done
  done


example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  constructor
  · have h : p ≥ 7 := by addarith[hp]
    calc p ^ 2 ≥ 7^2 := by rel[h]
      _ = 49 := by numbers
    done
  · addarith[hp]
  done


example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have ha : a≥ 6 := by addarith[h]
  constructor
  · assumption
  · calc 3*a ≥ 3*6 := by rel[ha]
      _ = 18 := by numbers
      _ ≥ 10 := by numbers
    done
  done


example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1,h2⟩ := h
  have hx : x = 5-y := by addarith[h1]
  rw [hx] at h2
  have hy : y = 2 := by
    calc y = (5-y+2*y) - 5 := by ring
      _ = 7 -5 := by rw[h2]
      _ = 2 := by numbers
    done
  constructor
  · rw [hy] at hx
    addarith [hx]
  · assumption
  done



example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by


  sorry
  done
