/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- le_or_succ_le n 1 : n ≤ 1 ∨ 2 ≤ n

-- eq_zero_or_eq_zero_of_mul_eq_zero  (h : a * b = 0) : a = 0 ∨ b = 0

-- ne_of_lt (h : a < b) : a ≠ b

-- syntaxe obtain (1)
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  · calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  · calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]
  done


-- syntaxe obtain (2)
example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := (le_or_succ_le n 1 : n ≤ 1 ∨ 2 ≤ n)
  obtain (hn : n ≤ 1) | (hn : 2 ≤ n) := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 ≥ 2^2 := by rel [hn]
      _ = 4 := by numbers
      _ > 2 := by numbers
    done
  done

-- right left (3)
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
  obtain (h21 : x - 1 = 0)|(h22: x - 2 = 0) := h2
  left
  addarith [h21]
  right
  addarith [h22]
  done

-- interessante
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
  obtain h1 | h2 := h
  have hx : x^2 = 16 := by
    calc x^2 = 4^2 := by rw [h1]
      _ = 16 := by numbers
    done
  addarith [hx]
  have hx : x^2 = 16 := by
    calc x^2 = (-4)^2 := by rw [h2]
      _ = 16 := by numbers
    done
  addarith [hx]
  done



example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  · calc x ^ 2 - 3 * x + 2 = 1^2 -3*1+2 := by rw [h1]
      _ = 0 := by numbers
    done
  · calc x ^ 2 - 3 * x + 2 = 2^2 -3*2+2 := by rw [h2]
      _ = 0 := by numbers
    done
  done



example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  · calc t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h1]
      _ = 0 := by numbers
    done
  · calc t ^ 2 - t - 6 = 3 ^ 2 - 3 - 6 := by rw [h2]
      _ = 0 := by numbers
    done
  done



-- different style of writing proofs
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h2 := h
  · rw [h1]
    ring
  · rw [h2]
    ring
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
  have hx : x = y / 2 - 1/2 := by addarith [h]
  left
  addarith [hx]
  done



example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : (x+3)*(x-1) = 0 := by
    calc (x+3)*(x-1) = x ^ 2 + 2 * x - 3 := by ring
      _ = 0 := by rw [hx]
    done
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  · left
    addarith [hx1]
  · right
    addarith [hx2]
  done



example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : a ^ 2 + 2 * b ^ 2 - 3 * a * b = 0 := by addarith [hab]
  have h2 : (b - a) * (2*b - a) = 0 := by
    calc (b - a) * (2*b - a) = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
      _ = 0 := by rw [h1]
    done
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain h | h' := h3
  · left
    addarith [h]
  · right
    addarith [h']
  done



example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have H : t^2 * (t-1) = 0 := by
    calc t^2 * (t-1) = t^3 - t^2 := by ring
      _  = 0 := by addarith [ht]
    done
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero H
  obtain h1 | h2 := h3
  · right
    cancel 2 at h1
  · left
    addarith [h2]
  done


-- more interesting
example {n : ℕ} : n ^ 2 ≠ 7 := by
  obtain h2 | h3 := (le_or_succ_le n 2)
  · apply ne_of_lt
    calc n^2 ≤ 2^2 := by rel [h2]
      _  < 7 := by numbers
    done
  · apply ne_of_gt
    calc n^2 ≥ 3^2 := by rel [h3]
      _ > 7 := by numbers
    done
  done


-- more interesting
example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 0
  obtain hn | hp := hx
  · apply ne_of_lt
    calc 2*x ≤ 0 := by addarith [hn]
      _ < 3 := by numbers
    done
  · have hx1 := le_or_succ_le x 1
    obtain h1 | h2 := hx1
    · apply ne_of_lt
      calc 2*x ≤ 2*1 := by rel [h1]
        _ < 3 := by numbers
      done
    · apply ne_of_gt
      calc 2*x ≥ 2*2 := by rel [h2]
        _ > 3 := by numbers
      done
  done



example {t : ℤ} : 5 * t ≠ 18 := by
  sorry
  done



example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm : m^2 + 4*m = m*(m+4) := by ring
  obtain h | h' := (le_or_succ_le m 5)
  · apply ne_of_lt
    rw [hm]
    calc m*(m+4) ≤ 5*(5+4) := by rel [h]
      _ = 45 := by numbers
      _ < 46 := by numbers
    done
  · apply ne_of_gt
    rw [hm]
    calc 46 < 60 := by numbers
      _ = 6*(6+4) := by numbers
      _ ≤ m*(m+4) := by rel [h']
    done
  done
