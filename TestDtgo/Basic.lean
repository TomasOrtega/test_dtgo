import Mathlib

open Finset BigOperators

variable {A B C b c η n1 n2 rtio: ℝ}
variable (hc_leq1 : c ≤ 1)
variable (hn1 : A * η^2 = n1) (hn2 : C * η^2 = n2) (hc : 1 - c / 2 = rtio)
variable {r e g: ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ rtio * r t + g t) (hg : ∀ t, g t = n1 + n2 * e t)

-- Asserting positivity of variables
variable (hA_pos : 0 ≤ A) (hB_pos : 0 < B) (hC_pos : 0 < C) (hb_pos : 0 < b) (hc_pos : 0 < c) (hη_pos : 0 < η)
variable (hr_nonneg : ∀ t, 0 ≤ r t) (he_nonneg : ∀ t, 0 ≤ e t)

lemma r_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t + 1) * r 0 := by
  have hrtio_pos : 0 < rtio := by rw [<-hc]; linarith [hc_pos];
  suffices h : r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t + 1 - 1 - s) * g s) + rtio^(t + 1) * r 0;
  rw [add_tsub_cancel_right] at h; exact h;
  induction (t + 1) with
  | zero => rw [Nat.zero_eq, range_zero, sum_empty, hr, mul_zero, add_zero];
  | succ i hi =>
  rw [Nat.succ_eq_add_one, hr, mul_zero, add_zero];
  rw [hr, mul_zero, add_zero] at hi;
  calc
    r (i + 1) ≤ rtio * r i + g i := by apply hrec;
    _ ≤ g i + rtio * (∑ s in range i, rtio^(i - 1 - s) * g s) := by simp only [add_comm, add_le_add_iff_left, gt_iff_lt, mul_le_mul_left, hrtio_pos, hi];
    _ = g i + ∑ s in range i, rtio^1 * rtio^(i - 1 - s) * g s  := by simp only [mul_sum, pow_one, mul_assoc];
    _ = g i + ∑ s in range i, rtio^(1 + i - 1 - s) * g s := by
      rw [add_right_inj, sum_congr (by rfl)];
      intros x hx;
      rw [<-pow_add, mul_eq_mul_right_iff];
      left;
      have hx_lt_i : x < i := mem_range.mp hx;
      rw [add_tsub_cancel_left, add_comm];
      cases i with
      | zero => apply not_lt_zero' at hx_lt_i; contradiction;
      | succ i => rw [Nat.succ_eq_add_one, add_tsub_cancel_right, add_comm, <-add_tsub_assoc_of_le (Nat.lt_succ.mp hx_lt_i), add_comm];
    _ = ∑ s in range (i + 1), rtio ^ (i + 1 - 1 - s) * g s := by rw [sum_range_succ, add_tsub_cancel_right, add_tsub_cancel_left, tsub_eq_zero_of_le (le_refl i), pow_zero, one_mul, add_comm _ (g i)];

lemma sum_le_inverse_one_minus_rtio (k : ℝ) (hk_lt1: k < 1) (hk_nonneg: 0 ≤ k) (my_finset : Finset ℕ) : ∑ s in my_finset, k^s ≤ (1 - k)⁻¹ := by
  let f : ℕ → ℝ := λ s ↦ k^s;
  have fnonneg : ∀ s ∉ my_finset, 0 ≤ f s := by simp only [mem_range, not_lt, pow_nonneg, implies_true, forall_const, hk_nonneg];
  have fs : f = λ s ↦ k^s := rfl;
  rw [<-tsum_geometric_of_lt_one hk_nonneg hk_lt1, <-fs];
  have f_summable : Summable f := by apply summable_geometric_of_lt_one hk_nonneg hk_lt1;
  apply sum_le_tsum _ fnonneg f_summable;

lemma r_lemma_expanded (t : ℕ): r (t + 1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s) := by
  calc
  r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t + 1) * r 0 := by apply r_lemma; repeat' assumption;
  _ = ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * e s)) := by simp only [hr, mul_zero, add_zero, hg];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * n1 + rtio^(t - s) * n2 * (e s)) := by rw [sum_congr (by rfl)]; intros; rw [mul_add, add_right_inj, mul_assoc];
  _ =  n1 * ∑ s in range (t + 1), rtio^(t - s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s) := by simp only [sum_add_distrib, mul_sum, mul_comm];
  _ =  n1 * ∑ s in range (t + 1), rtio^(s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s) := by rw [add_left_inj, mul_eq_mul_left_iff]; left; apply sum_range_reflect;
  _ ≤ n1 * (1 - rtio)⁻¹ + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s) := by
      rw [add_le_add_iff_right];
      have h : ∑ s in range (t + 1), rtio^(s) ≤ (1 - rtio)⁻¹ := by apply sum_le_inverse_one_minus_rtio rtio (by linarith) (by linarith);
      exact mul_le_mul_of_nonneg_left h (by rw [<-hn1]; positivity);
  _ = n1 * 2 / c + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s) := by rw [add_left_inj, <-hc, sub_sub_cancel, inv_div]; ring;
  _ = n1 * 2 / c + n2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s) := by rw [add_right_inj, hc, mul_comm, sum_mul, sum_congr (by rfl)]; intros; ring;
  _ ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s) := by rw [hn2, hn1];

lemma obvious_inequality (hη : η ≤ 1 / 2 * Real.sqrt (b * c / (B * C))) : B * C * η ^ 2 * (2 / c) ≤ b / 2 := by
  have h_sqrt : (Real.sqrt (b * c / (B * C))) ^ 2 = b * c / (B * C) := by rw [pow_two]; exact Real.mul_self_sqrt (by positivity);
  have h : η ^ 2 ≤  1/4 * b * c / (B * C) := by calc
    η ^ 2 ≤ (1 / 2 * Real.sqrt (b * c / (B * C))) ^ 2 := by apply pow_le_pow_left (by positivity) hη 2;
    _ = (1 / 2) ^ 2 * (Real.sqrt (b * c / (B * C))) ^ 2 := by rw [pow_two, pow_two]; ring;
    _ = 1/4 * b * c / (B * C) := by rw [h_sqrt]; ring;
  calc
    B * C * η ^ 2 * (2 / c) = B * C * (2 / c) * η ^ 2 := by ring;
    _ ≤ B * C * (2 / c) * (1/4 * b * c / (B * C)) := by apply mul_le_mul_of_nonneg_left h (by positivity);
    _ = b / 2 := by field_simp; ring;

lemma change_var_inequality (T : ℕ) : ∑ t in range T, ∑ s in range (t + 1), rtio ^ (t - s) * e s ≤ (1 - rtio)⁻¹ * ∑ t in range T, e t := by
  have hrtio_pos : 0 < rtio := by rw [<-hc]; linarith [hc_pos];
  calc
    ∑ t in range T, ∑ s in range (t + 1), rtio ^ (t - s) * e s = ∑ t in range T, ∑ s in range (t + 1), rtio ^ t * (rtio⁻¹)^s * e s := by
      rw [sum_congr (by rfl)];
      intros;
      rw [sum_congr (by rfl)];
      intros _ hs;
      rw [inv_pow, mul_eq_mul_right_iff]; -- this line and the next could be replaced by `congr`
      left;
      field_simp;
      rw [<-pow_add, Nat.sub_add_cancel (by linarith [mem_range.mp hs])];
    _ = ∑ t in range T, rtio ^ t * ∑ s in range (t + 1), (rtio⁻¹)^s * e s := by rw [sum_congr (by rfl)]; intros; rw [mul_sum, sum_congr (by rfl)]; intros; rw [mul_assoc];
    _ = ∑ n in range T, e n * ∑ k in range (T - n), rtio^k := by
      induction T with
      | zero => rw [range_zero, sum_empty, sum_empty];
      | succ i hi =>
      rw [sum_range_succ, sum_range_succ];
      have h: ∑ n in range (Nat.succ i), e n * ∑ k in range (Nat.succ i - n), rtio ^ k = ∑ n in range (Nat.succ i), e n * (∑ k in range (i - n), rtio ^ k + rtio ^ (i - n)) := by
        rw [sum_congr (by rfl)];
        intros x hx;
        rw [Nat.succ_eq_add_one] at hx;
        rw [<-sum_range_succ, Nat.succ_eq_add_one, add_comm, add_tsub_assoc_of_le (by linarith [mem_range.mp hx]), Nat.one_add (i - x)];
      rw [h, sum_range_succ, hi, tsub_eq_zero_of_le (by linarith), range_zero, sum_empty, pow_zero, zero_add, mul_one];
      have h: rtio ^ i * (∑ x in range i, rtio⁻¹ ^ x * e x + rtio⁻¹ ^ i * e i) = rtio ^ i * ∑ x in range i, rtio⁻¹ ^ x * e x + e i := by rw [mul_add, add_right_inj]; field_simp; ring;
      rw [h, <-add_assoc, add_left_inj];
      have h : ∑ x in range i, e x * (∑ k in range (i - x), rtio ^ k + rtio ^ (i - x)) = ∑ x in range i, (e x * ∑ k in range (i - x), rtio ^ k  + e x * rtio ^ (i - x)) := by rw [sum_congr (by rfl)]; intros; ring;
      rw [h, mul_sum, <-sum_add_distrib, sum_congr (by rfl)];
      intros _ hx;
      rw [add_right_inj]; ring_nf; rw [inv_pow, mul_eq_mul_right_iff]; left; field_simp; rw [<-pow_add, tsub_add_cancel_of_le (by linarith [mem_range.mp hx])];
    _ ≤  ∑ t in range T, e t * (1 - rtio)⁻¹ := by
      gcongr with t _;
      linarith [he_nonneg t];
      apply sum_le_inverse_one_minus_rtio rtio (by linarith [hc_leq1]) (by linarith [hc_pos]);
    _ = (1 - rtio)⁻¹ * ∑ t in range T, e t := by rw [mul_comm, sum_mul];

theorem your_theorem (T : ℕ) (hη : η ≤ (1/2) * Real.sqrt (b * c / (B * C))) : B * ∑ t in range T, r t ≤ B * A * η^2 * (2 / c) * T + (b/2) * ∑ t in range T, e t := calc
  B * ∑ t in range T, r t ≤ B * ∑ t in range T, r (t + 1) := by
    field_simp; -- divide both sides by B
    calc
      ∑ t in range T, r t ≤ -r 0 + ∑ t in range (T + 1), r t := by rw [hr, sum_range_succ, neg_zero, zero_add, le_add_iff_nonneg_right]; exact hr_nonneg T;
      _ = ∑ t in range T, r (t + 1) := by
        induction T with
        | zero => simp only [neg_zero, Nat.zero_eq, zero_add, range_one, sum_singleton, add_zero, range_zero, sum_empty, hr]
        | succ i hi => rw [sum_range_succ, <-add_assoc (-r 0) _ (r (i + 1)), hi, sum_range_succ]
  _ ≤ B * ∑ t in range T, (A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), ((1 - c / 2) ^ (t - s) * (e s))) := by gcongr with i _; apply r_lemma_expanded; repeat' assumption;
  _ = B * ∑ t in range T, (A * η^2 * 2 / c)  + B * ∑ t in range T, (C * η^2 * ∑ s in range (t + 1), ((1 - c / 2) ^ (t - s) * (e s)))  := by rw [sum_add_distrib, mul_add];
  _ = B * A * η^2 * (2 / c) * T + B * ∑ t in range T, (C * η^2 * ∑ s in range (t + 1), ((1 - c / 2) ^ (t - s) * (e s)))  := by rw [add_left_inj, sum_const, card_range]; ring;
  _ ≤ B * A * η^2 * (2 / c) * T + (b/2) * ∑ t in range T, e t  := by
    rw [add_le_add_iff_left];
    calc
      B * ∑ t in range T, (C * η^2 * ∑ s in range (t + 1), ((1 - c / 2) ^ (t - s) * (e s))) = B * C * η^2 * ∑ t in range T,( ∑ s in range (t + 1), ((1 - c / 2) ^ (t - s) * (e s))) := by rw [<-mul_sum]; ring;
      _ ≤  B * C * η^2 * ((2 / c) * ∑ t in range T, e t):= by
        apply mul_le_mul_of_nonneg_left _ (by positivity);
        have h : (2 / c) = (1 - (1 - c / 2))⁻¹ := by rw [sub_sub_cancel, inv_div];
        rw [h, hc];
        apply change_var_inequality hc_leq1 hc hc_pos he_nonneg;
      _ = B * C * η ^ 2 * (2 / c) * ∑ t in range T, e t := by ring;
      _ ≤  (b/2) * ∑ t in range T, e t := by
        have h : B * C * η ^ 2 * (2 / c) ≤ b / 2 := by apply obvious_inequality; repeat' assumption;
        have hpos :  0 ≤ ∑ t in range T, e t := by apply sum_nonneg; intro i _; exact he_nonneg i;
        exact mul_le_mul_of_nonneg_right h hpos;
