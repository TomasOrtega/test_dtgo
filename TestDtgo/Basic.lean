import Mathlib

open Finset BigOperators

variable {A B C b c : ℝ}
variable {η : ℝ} (hη : η ≤ (1/2) * sqrt (b * c / (B * C)))
variable {r e : ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ (1 - c/2) * r t + A * η^2 + C * η^2 * e t)
variable (hc : 0 < c ∧ c ≤ 1) (hB : 0 < B) (hb : 0 < b)

lemma my_first_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), ((1 - c/2)^(t - s) * (A * η^2 + C * η^2 * (e s))) + (1-c/2)^(t+1) * (r 0) := by
  induction t
  -- for the zero case, use hr and hrec to simplify the goal
  case zero => simp [hr, hrec]; sorry;
  case succ: d hd => sorry;




lemma my_lemma (t : ℕ): r (t+1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)  := calc
  r (t + 1) ≤ (1 - c/2) * r t + A * η^2 + C * η^2 * e t                                                               := by apply hrec;
  _ ≤ ∑ s in range (t + 1), ((1 - c/2)^(t - s) * (A * η^2 + C * η^2 * (e s))) + (1-c/2)^(t+1) * (r 0)                 := by sorry;
  _ ≤ ∑ s in range (t + 1), ((1 - c/2)^(t - s) * (A * η^2 + C * η^2 * (e s)))                                         := by simp only [hr, mul_zero, add_zero, le_refl];
  _ ≤ A * η^2 * ∑ s in range (t + 1), (1 - c/2)^(t - s) + C * η^2 * ∑ s in range (t + 1), ((e s) * (1 - c/2)^(t - s)) := by sorry;
  _ ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                                 := by sorry;



theorem your_theorem (T : ℕ) : B * ∑ t in range T, r t ≤ B * A * η^2 * (2/c) * T + (b/2) * ∑ t in range T, e t := sorry
