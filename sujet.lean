import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Function


/- SUJET VERSION C-/

/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/

/- exercices OR (1 + 1 points) -/

example {x : ℝ} (hx : 2 * x + 2 = 52) : x = 25 ∨ x = 12 := by
  sorry
  done

 example {x : ℝ} (h : x = -1 ∨ x = 4) : x ^ 2 - 3*x - 4 = 0 := by
  sorry
  done


/- exercices AND (1 + 1 points) -/

example {m n : ℤ} (H : 4 ≤ n ∧ m - 1 ≥  n) : m ≥ 5 := by
  sorry
  done

example {a : ℚ} (h : a - 2 ≥ 8) : a ≥ 4 ∧ 2 * a ≥ 10 := by
  sorry
  done



/- exercice CONTRADICTION (1 point) -/

example {x : ℤ} (h2 : x ≤ 7) (h : x + 2 = 42) : x < 2 := by
  sorry
  done


/- exercice INDUCTION (4 points) -/

example : ∀ n, (-1)^n = 1 ∨ (-1)^n = -1 := by
  sorry
  done



/- exercice INJECTIVE (4 points) -/

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ (f (2 * x) - 6) ) := by
  sorry
  done



/- exercice SURJECTIVE (4 points) -/

example : ∀ (f : ℚ → ℚ), Surjective f → Surjective (fun x ↦ (f (x-1)) ) := by
  sorry
  done


/- exercice INJECTIVE (4 points) -/

example : ¬ Injective (fun (x : ℤ) ↦ x^4) := by
  sorry
  done





/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/
