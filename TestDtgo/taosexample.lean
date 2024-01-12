import Mathlib

open Finset BigOperators

example (a D : ℕ → ℝ) (hD : ∀ k, a k ≤ D k - D (k+1)) (hpos : ∀ k, 0 ≤ D k) (ha : Antitone a) (k : ℕ)
  : a k ≤ D 0 / (k + 1) := calc
    a k = (∑ _i in range (k+1), a k) / (k+1)           := by field_simp; exact mul_comm (a k) (k + 1);
    _ ≤ (∑ i in range (k+1), a i) / (k+1)              := by gcongr with _ hi; apply ha; simp at hi; linarith;
    _ ≤ (∑ i in range (k+1), (D i - D (i+1))) / (k+1)  := by gcongr; apply hD;
    _ = (D 0 - D (k+1)) / (k+1)                        := by congr; exact sum_range_sub' (fun i => D i) (k + 1);
    _ ≤ D 0 / (k+1)                                    := by gcongr; linarith [hpos (k+1)];
