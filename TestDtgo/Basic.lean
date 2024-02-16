import Mathlib

open Finset BigOperators

variable {A B C b c η n1 n2 rtio: ℝ}
variable (hc_pos : c > 0) (hc_leq1 : c ≤ 1)
variable (hn1 : A * η^2 = n1) (hn2 : C * η^2 = n2) (hc : 1 - c / 2 = rtio)
variable {r e g: ℕ → ℝ} (hr : r 0 = 0) (hrec : ∀ t, r (t + 1) ≤ rtio * r t + g t) (hg : ∀ t, g t = n1 + n2 * e t)

-- Asserting positivity of variables
variable (hA_pos : A ≥ 0) (hB_pos : B > 0) (hC_pos : C > 0) (hb_pos : b > 0) (hc_pos : c > 0) (hη_pos : η > 0)
variable (hr_pos : ∀ t, r t ≥ 0) (he_pos : ∀ t, e t ≥ 0)

lemma r_lemma (t : ℕ): r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * r 0 := by {
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
  suffices h : r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t + 1 - 1 - s) * g s) + rtio^(t+1) * r 0;
  rw [add_tsub_cancel_right] at h; exact h;
  induction' (t + 1) with i hi
  -- case 0
  rw [Nat.zero_eq, range_zero, sum_empty, hr, mul_zero, add_zero];
  -- case succ
  rw [Nat.succ_eq_add_one, hr, mul_zero, add_zero];
  rw [hr, mul_zero, add_zero] at hi;
  calc
    r (i + 1) ≤ rtio * r i + g i := by apply hrec;
    _ = g i + rtio * r i  := by rw [add_comm];
    _ ≤ g i + rtio * (∑ s in range i, rtio^(i - 1 - s) * g s) := by simp only [add_le_add_iff_left, gt_iff_lt, mul_le_mul_left, hrtio_pos, hi];
    _ = g i + (∑ s in range i, rtio * (rtio^(i - 1 - s) * g s)) := by rw [mul_sum];
    _ = g i + ∑ s in range i, rtio^1 * rtio^(i - 1 - s) * g s  := by simp only [pow_one, mul_assoc];
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
      rw [Nat.succ_eq_add_one, add_tsub_cancel_right, add_comm, add_tsub_assoc_of_le _, add_comm];
      exact Nat.lt_succ.mp hx_lt_i;
    }
    _ = ∑ s in range (i + 1), rtio ^ (i + 1 - 1 - s) * g s := by {
      rw [sum_range_succ, add_comm _ (rtio ^ (i + 1 - 1 - i) * g i)];
      congr; rw [add_tsub_cancel_right, tsub_eq_zero_of_le, pow_zero, one_mul]; rfl;
      ext s; rw [add_tsub_cancel_right, add_tsub_cancel_left];
    }
}

lemma sum_le_inverse_one_minus_rtio (k : ℝ) (hk_lt1: k < 1) (hk_nonneg: 0 ≤ k) (my_finset : Finset ℕ) : ∑ s in my_finset, k^s ≤ (1 - k)⁻¹ := by
  let f : ℕ → ℝ := λ s ↦ k^s;
  have fnonnegaux : ∀ s ∉ my_finset, 0 ≤ f s := by simp only [mem_range, not_lt, pow_nonneg, implies_true, forall_const, hk_nonneg];
  have fs : f = λ s ↦ k^s := rfl;
  rw [<-tsum_geometric_of_lt_1 hk_nonneg hk_lt1, <-fs];
  have f_summable : Summable f := by apply summable_geometric_of_lt_1 hk_nonneg hk_lt1;
  apply sum_le_tsum _ fnonnegaux f_summable;

lemma my_lemma (t : ℕ): r (t+1) ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)  :=
  have hn1_nonneg : 0 ≤ n1 := by rw [<-hn1]; positivity;
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith;
  have hrtio_lt1 : rtio < 1 := by linarith;
  have hrtio_nonneg : 0 ≤ rtio := by linarith;
  calc
  r (t + 1) ≤ ∑ s in range (t + 1), (rtio^(t - s) * g s) + rtio^(t+1) * r 0          := by apply r_lemma (hc_leq1) (hc) (hr) (hrec) (hc_pos) (t);
  _ = ∑ s in range (t + 1), (rtio^(t - s) * g s)                                         := by rw [hr, mul_zero, add_zero];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * (n1 + n2 * e s))                                         := by simp only [hg];
  _ = ∑ s in range (t + 1), (rtio^(t - s) * n1 + rtio^(t - s) * n2 * (e s)) := by rw [sum_congr]; rfl; intros; rw [mul_add, add_right_inj, mul_assoc];
  _ =  ∑ s in range (t + 1), rtio^(t - s) * n1 + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by rw [sum_add_distrib];
  _ =  n1 * ∑ s in range (t + 1), rtio^(t - s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by simp only [mul_sum, mul_comm];
  _ =  n1 * ∑ s in range (t + 1), rtio^(s) + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)      := by {
    have h : ∑ s in range (t + 1), rtio^(t - s) = ∑ s in range (t + 1), rtio^(s) := by apply sum_range_reflect;
    rw [h];
  }
  _ ≤ n1 * (1 - rtio)⁻¹ + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by {
      have h : ∑ s in range (t + 1), rtio^(s) ≤ (1 - rtio)⁻¹ := by apply sum_le_inverse_one_minus_rtio rtio hrtio_lt1 hrtio_nonneg;
      nlinarith [h, hn1_nonneg];
    }
  _ ≤ n1 * 2 / c + ∑ s in range (t + 1), rtio^(t - s) * n2 * (e s)                            := by {
    rw[<-hc]; rw [sub_sub_cancel, inv_div, add_le_add_iff_right];
    have h : n1 * (2/c) = n1 * 2 / c := by symm; exact mul_div_assoc n1 2 c;
    simp only [le_refl, h];
  }
  _ = n1 * 2 / c + n2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                            := by {
    simp only [add_right_inj];
    rw [hc, mul_comm, sum_mul, sum_congr]; rfl;
    intro x _; ring;
  }
  _ ≤ A * η^2 * 2 / c + C * η^2 * ∑ s in range (t + 1), (1 - c / 2) ^ (t - s) * (e s)                  := by rw [hn2, hn1];

lemma last_step (hη : η ≤ 1 / 2 * Real.sqrt (b * c / (B * C))) : B * C * η ^ 2 * (2 / c) ≤ b / 2 := by
  -- Start with the assumption
  have h : (Real.sqrt (b * c / (B * C))) ^ 2 = b * c / (B * C) := by rw [pow_two]; exact Real.mul_self_sqrt (by positivity);
  have h₂ : η ^ 2 ≤  1/4 * b * c / (B * C) := by calc
    η ^ 2 ≤ (1 / 2 * Real.sqrt (b * c / (B * C))) ^ 2 := by apply pow_le_pow_left (by positivity) hη 2;
    _ = (1 / 2) ^ 2 * (Real.sqrt (b * c / (B * C))) ^ 2 := by rw [pow_two, pow_two]; ring;
    _ = 1/4 * b * c / (B * C) := by rw [h]; ring;
  calc
    B * C * η ^ 2 * (2 / c) = B * C * (2 / c) * η ^ 2 := by ring;
    _ ≤ B * C * (2 / c) * (1/4 * b * c / (B * C)) := by apply mul_le_mul_of_nonneg_left h₂ (by positivity);
    _ = b / 2 := by field_simp; ring;


lemma last_lemma (T : ℕ) : ∑ t in range T, ∑ s in range (t + 1), rtio ^ (t - s) * e s ≤ (1 - rtio)⁻¹ * ∑ t in range T, e t := by {
  have hrtio_pos : rtio > 0 := by rw [<-hc]; linarith [hc_pos];
  have hrtio_lt1 : rtio < 1 := by linarith [hrtio_pos, hc_leq1];
  have hrtio_nonneg : 0 ≤ rtio := by linarith [hrtio_pos];
  calc
    ∑ t in range T, ∑ s in range (t + 1), rtio ^ (t - s) * e s = ∑ t in range T, ∑ s in range (t + 1), rtio ^ t * (rtio⁻¹)^s * e s := by {
      rw [sum_congr]; rfl;
      intros t _;
      rw [sum_congr]; rfl;
      intros s hs;
      rw [mul_eq_mul_right_iff];
      left;
      suffices h : rtio ^ (t - s) = rtio ^ (t - s + s) * (rtio⁻¹)^s;
      rw [h, Nat.sub_add_cancel (by linarith [mem_range.mp hs])];
      rw [pow_add];
      field_simp;
    }
    _ = ∑ t in range T, rtio ^ t * ∑ s in range (t + 1), (rtio⁻¹)^s * e s := by congr; ext t; rw [mul_sum]; congr; ext s; rw [mul_assoc];
    _ = ∑ n in range T, e n * ∑ k in range (T - n), rtio^k := by {
      induction' T with i hi;
      -- case 0
      rw [range_zero, sum_empty, sum_empty];
      -- case succ
      rw [sum_range_succ, sum_range_succ];
      have h: ∀ n ≤ i, ∑ k in range (Nat.succ i - n), rtio ^ k = ∑ k in range (i - n), rtio ^ k + rtio ^ (i - n) := by {
        intros n hn;
        rw [<-sum_range_succ];
        congr;
        rw [Nat.succ_eq_add_one];
        rw [add_comm, add_tsub_assoc_of_le hn];
        ring;
      }
      have h2: ∑ n in range (Nat.succ i), e n * ∑ k in range (Nat.succ i - n), rtio ^ k = ∑ n in range (Nat.succ i), e n * (∑ k in range (i - n), rtio ^ k + rtio ^ (i - n)) := by {
        rw [sum_congr]; rfl;
        intros x hx;
        rw [h x (by linarith [mem_range.mp hx])];
      }
      rw [h2, sum_range_succ];
      rw [hi, tsub_eq_zero_of_le (by linarith), range_zero, sum_empty, pow_zero, zero_add, mul_one];
      have h: rtio ^ i * (∑ x in range i, rtio⁻¹ ^ x * e x + rtio⁻¹ ^ i * e i) = rtio ^ i * ∑ x in range i, rtio⁻¹ ^ x * e x + rtio ^ i * rtio⁻¹ ^ i * e i := by rw [mul_add (rtio ^ i) _ _]; ring;
      rw [h];
      have h: rtio ^ i * rtio⁻¹ ^ i * e i = e i := by field_simp;
      rw [h];
      rw [<-add_assoc];
      have h: rtio ^ i * ∑ x in range i, rtio⁻¹ ^ x * e x =  ∑ x in range i, rtio ^ i * rtio⁻¹ ^ x * e x := by rw [mul_sum]; congr; ext x; rw [mul_assoc];
      rw [h];
      have h: ∀ x ≤ i, rtio ^ (i - x) = rtio ^ i * rtio⁻¹ ^ x := by intros x hx; field_simp; rw [<-pow_add, add_comm, <-add_tsub_assoc_of_le hx, add_comm, add_tsub_cancel_right];
      have h2: ∑ x in range i, rtio ^ i * rtio⁻¹ ^ x * e x = ∑ x in range i, rtio ^ (i - x) * e x := by rw [sum_congr]; rfl; intros x hx; rw [<-h x (by linarith [mem_range.mp hx])];
      rw [h2, add_left_inj];
      have h : ∑ x in range i, e x * (∑ k in range (i - x), rtio ^ k + rtio ^ (i - x)) = ∑ x in range i, (e x * ∑ k in range (i - x), rtio ^ k + e x * rtio ^ (i - x)) := by congr; ext x; ring;
      rw [h, sum_add_distrib, add_right_inj, sum_congr]; rfl;
      intros; rw [mul_comm];
    }
    _ ≤  ∑ t in range T, e t * (1 - rtio)⁻¹ := by {
      gcongr with t _;
      linarith [he_pos t];
      apply sum_le_inverse_one_minus_rtio rtio hrtio_lt1 hrtio_nonneg;
    }
    _ = (1 - rtio)⁻¹ * ∑ t in range T, e t := by rw [mul_comm, sum_mul];
}


theorem your_theorem (T : ℕ) (hη : η ≤ (1/2) * Real.sqrt (b * c / (B * C))) : B * ∑ t in range T, r t ≤ B * A * η^2 * (2/c) * T + (b/2) * ∑ t in range T, e t := calc
  B * ∑ t in range T, r t ≤ B * ∑ t in range T, r (t + 1) := by {
    field_simp; -- divide both sides by B
    calc
      ∑ t in range T, r t ≤ -r 0 + ∑ t in range (T + 1), r t := by rw [hr, sum_range_succ, neg_zero, zero_add, le_add_iff_nonneg_right]; linarith [hr_pos T];
      _ = ∑ t in range T, r (t + 1) := by induction' T with i hi; simp only [neg_zero, Nat.zero_eq, zero_add, range_one, sum_singleton, add_zero, range_zero, sum_empty, hr]; rw [sum_range_succ, <-add_assoc (-r 0) _ (r (i + 1)), hi, sum_range_succ];
  }
  _ ≤ B * ∑ t in range T, (A * η^2 * 2 / c + C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) := by gcongr with i _; apply my_lemma (hc_leq1) (hn1) (hn2) (hc) (hr) (hrec) (hg) (hA_pos) (hc_pos) (hη_pos) (i);
  _ = B * ∑ t in range T, (A * η^2 * 2 / c)  + B * ∑ t in range T, (C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s)))  := by {
    let f : ℕ → ℝ := λ t ↦ C * η^2 * ∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s));
    let n3 := A * η^2 * 2 / c;
    have h : n3 = A * η^2 * 2 / c := rfl;
    rw [<-h];
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
      _ ≤  B * C * η^2 * ((2 / c) * ∑ t in range T, e t):= by {
        suffices h : ∑ t in range T, (∑ s in range (t+1), ((1 - c / 2) ^ (t - s) * (e s))) ≤ (2 / c) * ∑ t in range T, e t;
        apply mul_le_mul_of_nonneg_left h (by positivity);
        suffices h : ∑ t in range T, ∑ s in range (t + 1), rtio ^ (t - s) * e s ≤ (1 - rtio)⁻¹ * ∑ t in range T, e t;
        rw [<-hc] at h;
        have h2 : (1 - (1 - c / 2))⁻¹ = (2 / c) := by rw [sub_sub_cancel, inv_div];
        rw [<-h2];
        exact h;
        apply last_lemma hc_leq1 hc hc_pos he_pos;
      }
      _ = B * C * η ^ 2 * (2 / c) * ∑ t in range T, e t := by ring;
      _ ≤  (b/2) * ∑ t in range T, e t := by {
        have h : B * C * η ^ 2 * (2 / c) ≤ b / 2 := by apply last_step hc_pos hB_pos hC_pos hb_pos hη_pos hη;
        have hpos :  0 ≤ ∑ t in range T, e t := by apply sum_nonneg; intro i _; linarith [he_pos i];
        exact mul_le_mul_of_nonneg_right h hpos;
      }
  }
