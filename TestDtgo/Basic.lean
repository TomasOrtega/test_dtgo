import Mathlib

open Finset BigOperators

variable {A B C b c η n1 n2 rtio: ℝ}
variable (hc_pos : c > 0) (hc_leq1 : c ≤ 1)
variable (hn1 : A * η^2 = n1) (hn2 : C * η^2 = n2) (hc : 1 - c / 2 = rtio)
variable {r e g: ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ rtio * r t + g t) (hg : ∀ t, g t = n1 + n2 * e t)

-- Asserting positivity of variables
variable (hA_pos : A > 0) (hB_pos : B > 0) (hC_pos : C > 0) (hb_pos : b > 0) (hc_pos : c > 0) (hη_pos : η > 0)
variable (hr_pos : ∀ t, r t > 0) (he_pos : ∀ t, e t > 0)

lemma hn1_pos : n1 > 0 := calc
  n1 = A * η^2 := by exact hn1.symm;
  _ > 0       := by simp only [gt_iff_lt, hA_pos, mul_pos_iff_of_pos_left, hη_pos, pow_pos];

lemma hn2_pos : n2 > 0 := calc
  n2 = C * η^2 := by exact hn2.symm;
  _ > 0       := by simp only [gt_iff_lt, hC_pos, mul_pos_iff_of_pos_left, hη_pos, pow_pos];

lemma natural_valid_operations (n x : ℕ) (h_nat : n ≥ x) : n + 1 - x = n - x + 1 := by
  cases x
  rw [Nat.zero_eq, tsub_zero, tsub_zero];
  rw [add_comm, add_tsub_assoc_of_le h_nat, add_comm];


lemma my_third_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * r 0 := by {
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
  suffices h : r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t + 1 - 1 - s) * g s) + rtio^(t+1) * r 0;
  rw [add_tsub_cancel_right] at h; exact h;
  induction' (t + 1) with i hi
  -- case 0
  rw [Nat.zero_eq, range_zero, sum_empty, hr, mul_zero, add_zero];
  -- case succ
  rw [Nat.succ_eq_add_one, hr, mul_zero, add_zero]; -- sum_range_succ
  rw [hr, mul_zero, add_zero] at hi;
  calc
    r (i + 1) ≤ rtio * r i + g i := by apply hrec;
    _ = g i + rtio * r i  := by rw [add_comm];
    _ ≤ g i + rtio * (∑ s in range i, rtio^(i - 1 - s) * g s) := by simp only [add_le_add_iff_left,gt_iff_lt, mul_le_mul_left, hrtio_pos, hi];
    _ = g i + (∑ s in range i, rtio * (rtio^(i - 1 - s) * g s)) := by rw [mul_sum];
    _ = g i + ∑ s in range i, rtio^1 * rtio^(i - 1 - s) * g s  := by simp only [mul_assoc, pow_one];
    _ = g i + ∑ s in range i, rtio^(1 + i - 1 - s) * g s := by {
      rw [add_right_inj, <-sum_congr]; rfl;
      intros x hx;
      rw [<-pow_add];
      congr;
      have hx_lt_i : x < i := mem_range.mp hx;
      rw [add_tsub_cancel_left, add_comm];
      cases i -- Split into two cases: 0 and nat.succ i
      -- Case 0
      linarith;
      -- Case nat.succ i
      rw [Nat.succ_eq_add_one, add_tsub_cancel_right];
      apply natural_valid_operations;
      exact Nat.lt_succ.mp hx_lt_i;
    }
    _ = ∑ s in range (i + 1), rtio ^ (i + 1 - 1 - s) * g s := by {
      rw [sum_range_succ, add_comm (∑ x in range i, rtio ^ (i + 1 - 1 - x) * g x) (rtio ^ (i + 1 - 1 - i) * g i)];
      congr; rw [add_tsub_cancel_right, tsub_eq_zero_of_le, pow_zero, one_mul]; rfl;
      ext s; rw [add_tsub_cancel_right, add_tsub_cancel_left];
    }
}

lemma sum_le_inverse_one_minus_rtio (k : ℝ) (hk_lt1: k < 1) (hk_nonneg: 0 ≤ k ) : ∑ s in Finset.range (t + 1), k^s ≤ (1 - k)⁻¹ := by
  let f : ℕ → ℝ := λ s ↦ k^s;
  have fnonnegaux : ∀ s ∉ range (t + 1), 0 ≤ f s := by simp only [mem_range, not_lt, pow_nonneg, implies_true, forall_const, hk_nonneg];
  have fs : f = λ s ↦ k^s := rfl;
  rw [<-tsum_geometric_of_lt_1];
  rw [<-fs];
  have f_summable : Summable f := by apply summable_geometric_of_lt_1 hk_nonneg hk_lt1;
  apply sum_le_tsum _ fnonnegaux f_summable;
  exact hk_nonneg;
  exact hk_lt1;

lemma my_lemma (t : ℕ): r (t+1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)  :=
  have n1_pos : n1 > 0 := by apply hn1_pos hn1 hA_pos hη_pos;
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
  calc
  r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * r 0          := by apply my_third_lemma (hc_leq1) (hc) (hr) (hrec) (hc_pos) (t);
  _ = ∑ s in range (t + 1), (rtio^(t - s) * g s)                                         := by rw [hr, mul_zero, add_zero];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * e s))                                         := by simp only [hg];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * n1 + rtio^(t - s) * n2 * (e s)) := by rw [sum_range, sum_range]; congr; ext s; rw [mul_add, add_right_inj, mul_assoc];
  _ =  ∑ s in range (t + 1), rtio^(t - s) * n1 + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by rw [sum_add_distrib];
  _ =  n1 * ∑ s in range (t + 1), rtio^(t - s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by simp only [mul_sum, mul_comm];
  _ =  n1 * ∑ s in range (t + 1), rtio^(s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by {
    have h : ∑ s in range (t + 1), rtio^(t - s) = ∑ s in range (t + 1), rtio^(s) := by apply sum_range_reflect;
    rw [h];
  }
  _ ≤ n1 * (1 - rtio)⁻¹ + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by {
      have hrtio_nonneg : 0 ≤ rtio := by linarith [hrtio_pos];
      have hrtio_lt1 : rtio < 1 := by linarith [hrtio_pos, hrtio_nonneg];
      have h : ∑ s in range (t + 1), rtio^(s) ≤ (1 - rtio)⁻¹ := by apply sum_le_inverse_one_minus_rtio rtio hrtio_lt1 hrtio_nonneg;
      nlinarith [h, n1_pos];
    }
  _ ≤ n1 * 2 / c + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by {
    rw[<-hc]; rw [sub_sub_cancel, inv_div, add_le_add_iff_right];
    have h : n1 * (2/c) = n1 * 2 / c := by symm; exact mul_div_assoc n1 2 c;
    simp only [le_refl, h];
  }
  _ = n1 * 2 / c + n2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                            := by {
    simp only [add_right_inj];
    rw [hc, mul_comm, sum_mul, sum_congr];
    rfl;
    intro x _;
    ring;
  }
  _ ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                  := by rw [hn2, hn1];

theorem your_theorem (T : ℕ) (hη : η ≤ (1/2) * (b * c / (B * C))^(1/2)) : B * ∑ t in range T, r t ≤ B * A * η^2 * (2/c) * T + (b/2) * ∑ t in range T, e t := calc
  B * ∑ t in range T, r t ≤ B * ∑ t in range T, r (t + 1) := by {
    -- divide both sides by B;
    suffices h :  ∑ t in range T, r t ≤ ∑ t in range T, r (t+1);
    simp [*];
    calc
      ∑ t in range T, r t ≤ -r 0 + ∑ t in range (T + 1), r t := by rw [hr, sum_range_succ, neg_zero, zero_add, le_add_iff_nonneg_right]; linarith [hr_pos T];
      _ = ∑ t in range T, r (t + 1) := by induction' T with i hi; simp only [neg_zero, Nat.zero_eq, zero_add, range_one, sum_singleton, add_zero, range_zero, sum_empty, hr]; rw [sum_range_succ, <-add_assoc (-r 0) _ (r (i + 1))]; rw [hi, sum_range_succ];
  }
  _ ≤ B * ∑ t in range T, (A * η^2 * 2 / c + C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) := by gcongr with i hi; apply my_lemma (hc_leq1) (hn1) (hn2) (hc) (hr) (hrec) (hg) (hA_pos) (hc_pos) (hη_pos) (i);
  _ = B * ∑ t in range T, (A * η^2 * 2 / c)  + B * ∑ t in range T, (C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s)))  := by {
    let f : ℕ → ℝ := λ t ↦ C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s));
    let n3 := A * η^2 * 2 / c;
    have h1 : n3 = A * η^2 * 2 / c := rfl;
    rw [<-h1];
    have h2 : f = λ t ↦ C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s)) := rfl;
    rw [<-h2];
    suffices h2 : ∑ t in range T, (n3 + f t) = ∑ t in range T, n3 + ∑ t in range T, f t;
    rw [h2, mul_add];
    rw [sum_add_distrib];
  }
  _ = B * A * η^2 * (2/c) * T + B * ∑ t in range T, (C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s)))  := by rw [sum_const, card_range, nsmul_eq_mul, add_left_inj]; ring;
  _ ≤ B * A * η^2 * (2/c) * T + (b/2) * ∑ t in range T, e t  := by {
    suffices h : B * ∑ t in range T, (C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) ≤ (b/2) * ∑ t in range T, e t;
    rw [add_le_add_iff_left];
    exact h;
    calc
      B * ∑ t in range T, (C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) = B * C * η^2 * ∑ t in range T,( ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) := by rw [<-mul_sum]; ring;
      _ ≤  B * C * η^2 * c / 2 * 2 /c * ∑ t in range T,( ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) := by sorry;
      _ ≤  (b/2) * ∑ t in range T, e t := by sorry;
  }
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
