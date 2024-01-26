import Mathlib

open Finset BigOperators

variable {A B C b c η n1 n2 rtio: ℝ}
variable (hc_pos : c > 0) (hc_leq1 : c ≤ 1) -- (hη : η ≤ (1/2) * sqrt (b * c / (B * C)))
variable (hn1 : A * η^2 = n1) (hn2 : C * η^2 = n2) (hc : (1:ℝ) - c / (2:ℝ) = rtio)
variable {r e g: ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ rtio * r t + g t) (hg : ∀ t, g t = n1 + n2 * e t)

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

theorem my_example (ρ : ℝ) (i : ℕ) : ρ * (∑ s in range (i + 1), ρ ^ (i - s) ) = ∑ s in range (i + 1), ρ * ρ ^ (i - s) := by {
  let fs := λ s ↦ ρ^(i - s);
  have h1 : fs = λ s ↦ ρ^(i - s) := rfl;
  calc
    ρ * (∑ s in range (i + 1), ρ ^ (i - s) ) = ρ * (∑ s in range (i + 1), fs s) := by rw [h1];
    _ = ∑ s in range (i + 1), ρ * fs s := by rw [mul_sum];
}


lemma my_third_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * r 0 := by {
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
  have hrtio_nonneg : 0 ≤ rtio := by linarith [hrtio_pos];
  suffices h : r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t + 1 - 1 - s) * g s) + rtio^(t+1) * r 0;
  rw [add_tsub_cancel_right] at h; exact h;
  induction' (t + 1) with i hi
  -- replace Nat.zero for 0
  rw [Nat.zero_eq, range_zero, sum_empty, hr, mul_zero, add_zero];
  -- replace Nat.succ i for i + 1
  rw [Nat.succ_eq_add_one, hr, mul_zero, add_zero]; -- sum_range_succ
  rw [hr, mul_zero, add_zero] at hi;
  calc
    r (i + 1) ≤ g i + rtio * r i  := by linarith [hrec i];
    _ ≤ g i + rtio * (∑ s in range i, rtio^(i -1 - s) * g s) := by simp only [add_le_add_iff_left,gt_iff_lt, mul_le_mul_left, hrtio_pos, hi];
    _ = g i + (∑ s in range i, rtio * (rtio^(i - 1 - s) * g s)) := by rw [mul_sum];
    _ = g i + ∑ s in range i, rtio^1 * rtio^(i - 1 - s) * g s  := by simp only [mul_assoc, pow_one];
    _ = g i + ∑ s in range i, rtio^(1 + i - 1 - s) * g s := by simp only [add_right_inj]; congr; ext s; simp; left; nth_rw 1 [<-pow_one rtio]; rw [<-pow_add, add_comm]; sorry;
    _ = ∑ s in range (i + 1), rtio ^ (i + 1 - 1 - s) * g s := by {
      rw [sum_range_succ, add_comm (∑ x in range i, rtio ^ (i + 1 - 1 - x) * g x) (rtio ^ (i + 1 - 1 - i) * g i)];
      congr; simp only [add_tsub_cancel_right, ge_iff_le, le_refl, tsub_eq_zero_of_le, pow_zero, one_mul];
      ext s; simp only [add_tsub_cancel_left, add_tsub_cancel_right];
      }
}





lemma my_lemma (t : ℕ): r (t+1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)  := calc
  r (t + 1) ≤ rtio * r t + g t                                                               := by apply hrec;
  _ ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * (r 0)                    := by sorry;
  _ ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s)                                         := by simp only [hr, mul_zero, add_zero, le_refl];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * e s))                                         := by simp only [hg];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * n1 + rtio^(t - s) * n2 * (e s)) := by rw [sum_range, sum_range]; congr; ext s; simp only [mul_add, add_right_inj, mul_assoc];
  _ =  ∑ s in range (t + 1), rtio^(t - s) * n1 + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by rw [sum_add_distrib];
  _ =  n1 * ∑ s in range (t + 1), rtio^(t - s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by simp only [mul_sum, mul_comm];
  _ =  n1 * ∑ s in range (t + 1), rtio^(s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by sorry;
  _ ≤ n1 * (1 - rtio)⁻¹ + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by {
    have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
    have hrtio_nonneg : 0 ≤ rtio := by linarith [hrtio_pos];
    have hrtio_lt1 : rtio < 1 := by linarith [hrtio_pos, hrtio_nonneg];
    simp only [add_le_add_iff_right, ge_iff_le];
    sorry;
    -- simp [tsum_geometric_of_lt_1 hrtio_nonneg hrtio_lt1];
  };
  _ ≤ n1 * 2 / c + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by sorry;
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
