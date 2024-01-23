import Mathlib

open Finset BigOperators

variable {A B C b c η n1 n2 r rtio: ℝ}
variable (hc_pos : c > 0) (hc2 : c ≤ 1) (hη : η ≤ (1/2) * sqrt (b * c / (B * C)))
variable (hn1 : A * η^2 = n1) (hn2 : C * η^2 = n2) (hc : (1:ℝ) - c / (2:ℝ) = rtio)
variable {r e : ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ rtio * r t + n1 + n2 * e t)

-- Asserting positivity of variables
variable (hA_pos : A > 0) (hB_pos : B > 0) (hC_pos : C > 0) (hb_pos : b > 0) (hc_pos : c > 0) (hη_pos : η > 0)
variable (hr_pos : ∀ t, r t > 0) (he_pos : ∀ t, e t > 0)

theorem hn1_pos : n1 > 0 := calc
  n1 = A * η^2 := by exact hn1.symm;
  _ > 0       := by simp only [gt_iff_lt, hA_pos, mul_pos_iff_of_pos_left, hη_pos, pow_pos];

theorem hn2_pos : n2 > 0 := calc
  n2 = C * η^2 := by exact hn2.symm;
  _ > 0       := by simp only [gt_iff_lt, hC_pos, mul_pos_iff_of_pos_left, hη_pos, pow_pos];

-- theorem rtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos, hc2];

lemma my_first_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * (e s))) + rtio^(t+1) * (r 0) :=
-- have ratio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos, hc2];
calc
  r (t + 1) ≤ rtio * r t + n1 + n2 * e t                                                               := by apply hrec;
  _ ≤ ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * (e s))) + rtio^(t+1) * (r 0)                    := by {
    induction' t with i hi
    simp [hr];
    rw [Nat.succ_eq_add_one, sum_range_succ, sum_range_succ];
    simp [hr] at hi;
    simp [hr];
    -- divide both sides by rtio
    gcongr;
    sorry;
  }

lemma my_second_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * (e s))) := sorry
-- induction should work here





lemma my_lemma (t : ℕ): r (t+1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)  := calc
  r (t + 1) ≤ rtio * r t + n1 + n2 * e t                                                               := by apply hrec;
  _ ≤ ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * (e s))) + rtio^(t+1) * (r 0)                    := by {
    induction' t with i hi
    simp [hr];
    rw [Nat.succ_eq_add_one, sum_range_succ, sum_range_succ];
    simp [hr] at hi;
    simp [hr];
    -- substitute r (i + 1) with rtio * r t + n1 + n2 * e t using hrec
    sorry;
  }
  _ ≤ ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * (e s)))                                         := by simp only [hr, mul_zero, add_zero, le_refl];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * n1 + rtio^(t - s) * n2 * (e s)) := by rw [sum_range, sum_range]; congr; ext s; simp only [mul_add, add_right_inj, mul_assoc];
  _ = n1 * ∑ s in range (t + 1), rtio^(t - s) + ∑ s in range (t + 1), (rtio^(t - s) * n2 * (e s))      := by rw [sum_range, sum_range, sum_range]; congr; sorry;
  _ ≤ n1 * 2 / c + n2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                            := by sorry;
  _ ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                  := by rw [hn2, hn1];



theorem your_theorem (T : ℕ) : B * ∑ t in range T, r t ≤ B * A * η^2 * (2/c) * T + (b/2) * ∑ t in range T, e t := sorry
  --by rw [sum_range, sum_range]; congr; ext s; simp [mul_add]; simp [mul_assoc];


--      let n1 := A * η^2;
  --    have h1 : n1 = A * η^2 := rfl;
    --  rw [<-h1];
   --   let fs := λ s ↦ rtio^(t - s);
     -- have h2 : fs = λ s ↦ rtio^(t - s) := rfl;
     -- rw [<-h2];
     -- let fe := λ s ↦ n2 * (e s);
     -- have h3 : fe = λ s ↦ n2 * (e s) := rfl;
     -- rw [<-h3];
   -- }
