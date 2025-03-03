/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
set_option pp.funBinderTypes true

open Function

-- `comp_apply : (g ∘ f) x = g (f x)`

def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rw [comp_apply]
    _ = 2 * (x + 3) := by dsimp [f, g]
    _ = 2 * x + 6 := by ring
    _ = h x := by dsimp [h]
  done

def s (x : ℝ) : ℝ := 5 - x

example : s ∘ s = id := by
  ext x
  dsimp [s]
  ring
  done

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rw [comp_apply]
      _ = f x := by apply hg
      _ = f (id x) := by dsimp [id]
  · -- prove `f ∘ g = id`
    ext y
    apply hg
  done

theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by dsimp [id]
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rw [comp_apply]
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rw [comp_apply]
      _ = id x2 := by rw [hgf]
      _ = x2 := by dsimp [id]
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rw [comp_apply]
      _ = id y := by rw [hfg]
      _ = y := by dsimp [id]

theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H


/-! # Exercises -/


def u (x : ℝ) : ℝ := 5 * x + 1

-- Il faut trouver la bonne définition!
noncomputable def v (x : ℝ) : ℝ := (x - 1)/5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    dsimp [u, v]
    ring
  · ext x
    dsimp [u, v]
    ring
  done

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at hf hg ⊢
  intro a b hab
  apply hf
  apply hg
  assumption
  done

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at hf hg ⊢
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [hx, hy]
  done

example {X Y : Type} {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · assumption
  · assumption
  done

example {X Y : Type} {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at h1 h2
  obtain ⟨h3, h4⟩ := h1
  obtain ⟨h5, h6⟩ := h2
  ext y
  calc g1 y = g1 (id y) := by dsimp [id]
    _ = g1 ((f ∘ g2) y) := by rw [h6]
    _ = g1 (f (g2 y)) := by rw [comp_apply]
    _ = (g1 ∘ f) (g2 y) := by rw [comp_apply]
    _ = id (g2 y) := by rw [h3]
    _ = g2 y := by dsimp [id]
  done
