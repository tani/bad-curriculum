theory Adam_Asymptotics
  imports Adam_Realizable Adam_Order_Only
begin

section \<open>Power-law scales for exact Adam and AdamW\<close>

definition rz_power_kappa :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_kappa a k = 1 / real (power_population a k)"

definition rz_power_prefix_radius :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_prefix_radius a k =
    sqrt (real (power_population a k) / 2 *
      ln (2 * real (power_population a k) / power_confidence k))"

definition rz_power_u_bound ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_u_bound a b eps k =
    real (power_population a k) * power_learning_rate b k *
      (rz_power_kappa a k)^2 / eps"

definition rz_power_track_slack ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_track_slack a b beta1 eps k =
    beta1 * power_learning_rate b k /
      (2 * eps * (1-beta1)) + rz_power_u_bound a b eps k / 4"

definition rz_power_drift_error ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_drift_error a b beta1 eps k =
    (power_learning_rate b k / eps) *
      (2 * rz_power_prefix_radius a k + beta1/(1-beta1))"

definition rz_safe_delta :: "real \<Rightarrow> real \<Rightarrow> real" where
  "rz_safe_delta eps decay =
    min 1 (sigmoid (-1) / (4 * (1+eps) * (decay+1)))"

definition rz_power_drift_coeff ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_drift_coeff a b c beta1 eps decay k =
    sigmoid (-rz_safe_delta eps decay)/(1+eps) -
      decay * rz_safe_delta eps decay -
      rz_power_track_slack a b beta1 eps k / eps -
      power_tail_ratio a c k / eps"

definition rz_power_anchor_bound ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_anchor_bound a b c beta1 eps k =
    ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k / eps) - 1)) +
    real (power_anchor a c k) * (power_learning_rate b k / eps) *
      rz_power_track_slack a b beta1 eps k"

definition rz_tail_floor :: real where
  "rz_tail_floor = sigmoid (-1)"

definition rz_terminal_rate :: "real \<Rightarrow> real \<Rightarrow> real" where
  "rz_terminal_rate beta1 eps =
    (1-beta1) * sigmoid (-2) / (1+eps)"

definition rz_burn_index :: "real \<Rightarrow> nat" where
  "rz_burn_index beta =
    (SOME J. beta^J \<le> rz_tail_floor / (2*(1+rz_tail_floor)))"

lemma rz_tail_floor_positive: "0 < rz_tail_floor"
  unfolding rz_tail_floor_def by (rule sigmoid_pos)

lemma rz_tail_floor_at_most_one: "rz_tail_floor \<le> 1"
  unfolding rz_tail_floor_def by (rule sigmoid_le_one)

lemma rz_burn_index_spec:
  assumes beta0: "0 \<le> beta" and beta1: "beta < 1"
  shows "beta^(rz_burn_index beta) \<le>
    rz_tail_floor/(2*(1+rz_tail_floor))"
proof -
  have abs_beta: "abs beta < 1" using beta0 beta1 by simp
  have identity_filter: "filterlim (\<lambda>n::nat. n) sequentially sequentially"
    by (rule filterlim_ident)
  have limit: "((\<lambda>n. beta^n) \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_power_zero[OF identity_filter])
      (use abs_beta in simp)
  have denominator_positive: "0 < 2*(1+rz_tail_floor)"
    using rz_tail_floor_positive by simp
  have target_positive: "0 < rz_tail_floor/(2*(1+rz_tail_floor))"
    by (rule divide_pos_pos[OF rz_tail_floor_positive denominator_positive])
  have eventually_small: "\<forall>\<^sub>F n in sequentially.
      beta^n < rz_tail_floor/(2*(1+rz_tail_floor))"
    using order_tendstoD(2)[OF limit target_positive] by simp
  obtain J where small: "beta^J < rz_tail_floor/(2*(1+rz_tail_floor))"
    using eventually_small unfolding eventually_sequentially by blast
  have existence: "\<exists>J. beta^J \<le> rz_tail_floor/(2*(1+rz_tail_floor))"
    using small by (intro exI[of _ J]) linarith
  show ?thesis unfolding rz_burn_index_def by (rule someI_ex[OF existence])
qed

lemma rz_safe_delta_positive:
  assumes eps: "0 < eps" and decay: "0 \<le> decay"
  shows "0 < rz_safe_delta eps decay"
proof -
  have first: "0 < (1::real)" by simp
  have denominator: "0 < 4 * (1+eps) * (decay+1)"
    using eps decay by simp
  have second: "0 < sigmoid (-1) / (4 * (1+eps) * (decay+1))"
    by (rule divide_pos_pos[OF sigmoid_pos denominator])
  show ?thesis unfolding rz_safe_delta_def using first second by simp
qed

lemma rz_safe_delta_at_most_one:
  "rz_safe_delta eps decay \<le> 1"
  unfolding rz_safe_delta_def by simp

lemma rz_terminal_rate_positive:
  assumes beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "0 < rz_terminal_rate beta1 eps"
proof -
  have numerator: "0 < (1-beta1) * sigmoid (-2)"
    by (rule mult_pos_pos) (use beta1 sigmoid_pos[of "-2"] in auto)
  have denominator: "0 < 1+eps" using eps by linarith
  show ?thesis unfolding rz_terminal_rate_def
    by (rule divide_pos_pos[OF numerator denominator])
qed

section \<open>Elementary limits\<close>

lemma power_learning_rate_tendsto_zero:
  assumes noise: "a < 2*b"
  shows "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
proof -
  have bpos: "0 < b" using noise by arith
  show ?thesis unfolding power_learning_rate_def
    by (rule inverse_curriculum_power_tendsto_zero[OF bpos])
qed

lemma power_population_inverse_tendsto_zero:
  assumes tail: "c < a"
  shows "((\<lambda>k. 1 / real (power_population a k)) \<longlongrightarrow> 0) sequentially"
proof -
  have apos: "0 < a" using tail by arith
  show ?thesis unfolding power_population_def of_nat_power
    by (rule inverse_curriculum_power_tendsto_zero[OF apos])
qed

lemma rz_power_kappa_positive: "0 < rz_power_kappa a k"
  unfolding rz_power_kappa_def using power_population_positive[of a k] by simp

lemma rz_power_kappa_tendsto_zero:
  assumes tail: "c < a"
  shows "((\<lambda>k. rz_power_kappa a k) \<longlongrightarrow> 0) sequentially"
  unfolding rz_power_kappa_def
  by (rule power_population_inverse_tendsto_zero[OF tail])

lemma rz_power_u_exact:
  "rz_power_u_bound a b eps k =
    power_learning_rate b k / (eps * real (power_population a k))"
proof -
  have population_nonzero: "real (power_population a k) \<noteq> 0"
    using power_population_positive[of a k] by simp
  show ?thesis
    unfolding rz_power_u_bound_def rz_power_kappa_def
    using population_nonzero by (simp add: power2_eq_square field_simps; algebra)
qed

lemma rz_power_u_tendsto_zero:
  assumes noise: "a < 2*b" and tail: "c < a" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_u_bound a b eps k) \<longlongrightarrow> 0) sequentially"
proof -
  have eta: "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have inverse_population:
      "((\<lambda>k. 1 / real (power_population a k)) \<longlongrightarrow> 0) sequentially"
    by (rule power_population_inverse_tendsto_zero[OF tail])
  have product: "((\<lambda>k. power_learning_rate b k *
      (1 / real (power_population a k))) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF eta inverse_population] by simp
  have scaled: "((\<lambda>k. (1/eps) *
      (power_learning_rate b k * (1/real (power_population a k))))
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const product, of "1/eps"] by simp
  show ?thesis using scaled by (simp add: rz_power_u_exact algebra_simps)
qed

lemma rz_power_u_over_eta_tendsto_zero:
  assumes tail: "c < a" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_u_bound a b eps k / power_learning_rate b k)
      \<longlongrightarrow> 0) sequentially"
proof -
  have inverse_population:
      "((\<lambda>k. 1/real (power_population a k)) \<longlongrightarrow> 0) sequentially"
    by (rule power_population_inverse_tendsto_zero[OF tail])
  have scaled: "((\<lambda>k. (1/eps) * (1/real (power_population a k)))
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const inverse_population, of "1/eps"] by simp
  have eta_nonzero: "power_learning_rate b k \<noteq> 0" for k
    using power_learning_rate_positive[of b k] by simp
  show ?thesis using scaled eta_nonzero
    by (simp add: rz_power_u_exact algebra_simps)
qed

lemma rz_power_track_slack_tendsto_zero:
  assumes noise: "a < 2*b" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_track_slack a b beta1 eps k)
      \<longlongrightarrow> 0) sequentially"
proof -
  have eta: "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have first: "((\<lambda>k. beta1/(2*eps*(1-beta1)) * power_learning_rate b k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const eta, of "beta1/(2*eps*(1-beta1))"] by simp
  have auxiliary: "((\<lambda>k. rz_power_u_bound a b eps k)
      \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_u_tendsto_zero[OF noise tail eps])
  have second: "((\<lambda>k. (1/4)*rz_power_u_bound a b eps k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const auxiliary, of "1/4"] by simp
  have sum: "((\<lambda>k.
      beta1/(2*eps*(1-beta1))*power_learning_rate b k +
      (1/4)*rz_power_u_bound a b eps k) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF first second] by simp
  show ?thesis using sum
    by (simp add: rz_power_track_slack_def algebra_simps)
qed

lemma rz_power_prefix_radius_identity:
  "power_learning_rate b k * rz_power_prefix_radius a k =
    power_random_error a b k"
  unfolding rz_power_prefix_radius_def power_random_error_def by simp

lemma rz_power_drift_error_tendsto_zero:
  assumes noise: "a < 2*b" and beta0: "0 \<le> beta1"
    and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_drift_error a b beta1 eps k)
      \<longlongrightarrow> 0) sequentially"
proof -
  have random_error: "((\<lambda>k. power_random_error a b k)
      \<longlongrightarrow> 0) sequentially"
    by (rule power_random_error_tendsto_zero[OF noise])
  have eta: "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have first: "((\<lambda>k. (2/eps)*power_random_error a b k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const random_error, of "2/eps"] by simp
  have second: "((\<lambda>k. (beta1/(eps*(1-beta1))) * power_learning_rate b k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const eta,
      of "beta1/(eps*(1-beta1))"] by simp
  have sum: "((\<lambda>k. (2/eps)*power_random_error a b k +
      (beta1/(eps*(1-beta1)))*power_learning_rate b k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF first second] by simp
  show ?thesis
  proof (rule Lim_transform_eventually[OF sum])
show "\<forall>\<^sub>F k in sequentially.
      (2/eps)*power_random_error a b k +
        (beta1/(eps*(1-beta1)))*power_learning_rate b k =
      rz_power_drift_error a b beta1 eps k"
      by (intro always_eventually allI)
        (simp add: rz_power_drift_error_def
          rz_power_prefix_radius_identity[symmetric] algebra_simps)  qed
qed

lemma rz_power_error_coeff_tendsto_zero:
  assumes noise: "a < 2*b" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_track_slack a b beta1 eps k/eps +
      power_tail_ratio a c k/eps) \<longlongrightarrow> 0) sequentially"
proof -
  have slack: "((\<lambda>k. rz_power_track_slack a b beta1 eps k)
      \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_track_slack_tendsto_zero[OF noise tail beta0 beta1 eps])
  have ratio: "((\<lambda>k. power_tail_ratio a c k)
      \<longlongrightarrow> 0) sequentially"
    by (rule power_tail_ratio_tendsto_zero[OF tail])
  have slack_scaled: "((\<lambda>k. rz_power_track_slack a b beta1 eps k/eps)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_divide[OF slack tendsto_const, of eps] eps by simp
  have ratio_scaled: "((\<lambda>k. power_tail_ratio a c k/eps)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_divide[OF ratio tendsto_const, of eps] eps by simp
  show ?thesis using tendsto_add[OF slack_scaled ratio_scaled] by simp
qed

lemma rz_safe_delta_base_drift:
  assumes eps: "0 < eps" and decay: "0 \<le> decay"
  shows "3 * sigmoid (-1) / (4*(1+eps)) \<le>
    sigmoid (-rz_safe_delta eps decay)/(1+eps) -
      decay*rz_safe_delta eps decay"
proof -
  let ?q = "sigmoid (-1)"
  let ?delta = "rz_safe_delta eps decay"
  have q_positive: "0 < ?q" by (rule sigmoid_pos)
  have one_eps_positive: "0 < 1+eps" using eps by linarith
  have decay_one_positive: "0 < decay+1" using decay by linarith
  have delta_le_one: "?delta \<le> 1" by (rule rz_safe_delta_at_most_one)
  have mono: "?q \<le> sigmoid (-?delta)"
    using sigmoid_difference_bounds(1)[of "-1" "-?delta"] delta_le_one by simp
  have delta_cap: "?delta \<le> ?q/(4*(1+eps)*(decay+1))"
    unfolding rz_safe_delta_def by simp
  have decay_ratio_nonnegative: "0 \<le> decay/(decay+1)"
    by (rule divide_nonneg_pos[OF decay decay_one_positive])
  have decay_ratio: "decay/(decay+1) \<le> 1"
    using decay decay_one_positive by (simp add: divide_le_eq)
  have decay_bound: "decay*?delta \<le> ?q/(4*(1+eps))"
  proof -
    have first: "decay*?delta \<le> decay*(?q/(4*(1+eps)*(decay+1)))"
      by (rule mult_left_mono[OF delta_cap decay])
    have identity: "decay*(?q/(4*(1+eps)*(decay+1))) =
        (?q/(4*(1+eps))) * (decay/(decay+1))"
      using one_eps_positive decay_one_positive
      by (simp add: field_simps; algebra)
    have coefficient_nonnegative: "0 \<le> ?q/(4*(1+eps))"
      by (rule divide_nonneg_pos) (use q_positive one_eps_positive in auto)
have second_raw: "(?q/(4*(1+eps))) * (decay/(decay+1)) \<le>
        (?q/(4*(1+eps))) * 1"
      by (rule mult_left_mono[OF decay_ratio coefficient_nonnegative])
    have second: "(?q/(4*(1+eps))) * (decay/(decay+1)) \<le>
        ?q/(4*(1+eps))"
using second_raw by simp
    show ?thesis using first second identity by linarith
  qed
  have sigmoid_bound: "?q/(1+eps) \<le> sigmoid (-?delta)/(1+eps)"
    by (rule divide_right_mono[OF mono]) (use one_eps_positive in linarith)
have one_eps_nonzero: "1+eps \<noteq> 0" using one_eps_positive by linarith
  have quarter_identity: "3*?q/(4*(1+eps)) =
      ?q/(1+eps) - ?q/(4*(1+eps))"
    using one_eps_nonzero by (simp add: divide_simps; algebra)
  have sigmoid_step: "?q/(1+eps) - ?q/(4*(1+eps)) \<le>
      sigmoid (-?delta)/(1+eps) - ?q/(4*(1+eps))"
    using add_right_mono[OF sigmoid_bound, of "- ?q/(4*(1+eps))"]
    by simp
  have decay_step: "sigmoid (-?delta)/(1+eps) - ?q/(4*(1+eps)) \<le>
      sigmoid (-?delta)/(1+eps) - decay*?delta"
by (rule diff_mono[OF order_refl decay_bound])  show ?thesis
    unfolding quarter_identity
    by (rule order_trans[OF sigmoid_step decay_step])
qed

lemma rz_power_drift_coeff_eventually_positive:
  assumes noise: "a < 2*b" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    sigmoid (-1)/(2*(1+eps)) \<le>
      rz_power_drift_coeff a b c beta1 eps decay k"
proof -
  let ?q = "sigmoid (-1)"
  let ?base = "sigmoid (-rz_safe_delta eps decay)/(1+eps)-
    decay*rz_safe_delta eps decay"
  have base: "3*?q/(4*(1+eps)) \<le> ?base"
    by (rule rz_safe_delta_base_drift[OF eps decay])
  have one_eps_positive: "0 < 1+eps" using eps by linarith
  have threshold_positive: "0 < ?q/(4*(1+eps))"
    by (rule divide_pos_pos) (use sigmoid_pos[of "-1"] one_eps_positive in auto)
  have error_limit: "((\<lambda>k. rz_power_track_slack a b beta1 eps k/eps+
      power_tail_ratio a c k/eps) \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_error_coeff_tendsto_zero[OF noise tail beta0 beta1 eps])
  have eventually_small: "\<forall>\<^sub>F k in sequentially.
      rz_power_track_slack a b beta1 eps k/eps+
        power_tail_ratio a c k/eps < ?q/(4*(1+eps))"
    using order_tendstoD(2)[OF error_limit threshold_positive] by simp
have one_eps_nonzero: "1+eps \<noteq> 0" using one_eps_positive by linarith
  have half_identity: "?q/(2*(1+eps)) =
      3*?q/(4*(1+eps)) - ?q/(4*(1+eps))"
    using one_eps_nonzero by (simp add: divide_simps; algebra)
  show ?thesis
  proof (rule eventually_mono[OF eventually_small])
    fix k
    let ?error = "rz_power_track_slack a b beta1 eps k/eps +
      power_tail_ratio a c k/eps"
    assume error: "?error < ?q/(4*(1+eps))"
    have base_step: "3*?q/(4*(1+eps)) - ?q/(4*(1+eps)) \<le>
        ?base - ?q/(4*(1+eps))"
      by (rule diff_mono[OF base order_refl])
    have error_step: "?base - ?q/(4*(1+eps)) \<le> ?base - ?error"
      by (rule diff_mono[OF order_refl less_imp_le[OF error]])
    have coefficient_identity: "?base - ?error =
        rz_power_drift_coeff a b c beta1 eps decay k"
      unfolding rz_power_drift_coeff_def by algebra
    show "?q/(2*(1+eps)) \<le>
      rz_power_drift_coeff a b c beta1 eps decay k"
      unfolding half_identity coefficient_identity[symmetric]
      by (rule order_trans[OF base_step error_step])
  qed
qed

section \<open>Anchor term is negligible compared with the Tail mass\<close>

lemma rz_power_alpha_eventually_at_most_one:
  assumes noise: "a < 2*b" and eps: "0 < eps"
  shows "\<forall>\<^sub>F k in sequentially. power_learning_rate b k/eps \<le> 1"
proof -
  have limit: "((\<lambda>k. power_learning_rate b k/eps) \<longlongrightarrow> 0) sequentially"
    using tendsto_divide[OF power_learning_rate_tendsto_zero[OF noise]
      tendsto_const, of eps] eps by simp
  have eventually_strict:
      "\<forall>\<^sub>F k in sequentially. power_learning_rate b k/eps < 1"
    using order_tendstoD(2)[OF limit, of 1] by simp
  show ?thesis
    by (rule eventually_mono[OF eventually_strict]) linarith
qed

lemma rz_power_anchor_log_upper:
  assumes tail: "c < a"
    and alpha_at_most_one: "power_learning_rate b k/eps \<le> 1"
    and eps: "0 < eps"
  shows "ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k/eps)-1)) \<le>
    1 + real a * ln (real (curriculum_scale k))"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?N = "power_population a k"
  let ?n = "power_anchor a c k"
  let ?h = "power_learning_rate b k/eps"
  have K_positive: "0 < ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have N_positive: "0 < ?N" by (rule power_population_positive)
  have h_positive: "0 < ?h"
    by (rule divide_pos_pos[OF power_learning_rate_positive eps])
  have exp_nonnegative: "0 \<le> exp ?h - 1" using h_positive by simp
  have exp_upper: "exp ?h - 1 \<le> exp 1 - 1"
    using alpha_at_most_one by simp
  have anchor_le_population: "?n \<le> ?N"
    using power_counts[OF tail, of k] by arith
  have scaled:
      "real ?n * (exp ?h-1) \<le> real ?N * (exp 1-1)"
  proof -
    have "real ?n * (exp ?h-1) \<le> real ?N * (exp ?h-1)"
      by (rule mult_right_mono) (use anchor_le_population exp_nonnegative in simp_all)
    also have "... \<le> real ?N * (exp 1-1)"
      by (rule mult_left_mono[OF exp_upper]) simp
    finally show ?thesis .
  qed
  have population_at_least_one: "1 \<le> real ?N" using N_positive by simp
  have argument_upper:
      "1 + real ?n*(exp ?h-1) \<le> exp 1 * real ?N"
  proof -
    have "1 + real ?n*(exp ?h-1) \<le> 1 + real ?N*(exp 1-1)"
      using scaled by linarith
    also have "... \<le> exp 1 * real ?N"
      using population_at_least_one by (simp add: algebra_simps; linarith)
    finally show ?thesis .
  qed
have product_nonnegative: "0 \<le> real ?n * (exp ?h-1)"
    by (rule mult_nonneg_nonneg) (use exp_nonnegative in simp_all)
  have argument_positive: "0 < 1 + real ?n*(exp ?h-1)"
    using product_nonnegative by linarith  have logarithm:
      "ln (1 + real ?n*(exp ?h-1)) \<le> ln (exp 1 * real ?N)"
    by (rule ln_mono[OF argument_upper argument_positive])
  have population_cast: "real ?N = ?K^a"
    unfolding power_population_def by simp
  have logarithm_identity:
      "ln (exp 1 * real ?N) = 1 + real a * ln ?K"
    unfolding population_cast using K_positive
    by (simp add: ln_mult ln_realpow)
  show ?thesis using logarithm logarithm_identity by simp
qed

lemma rz_power_u_positive:
  assumes eps: "0 < eps"
  shows "0 < rz_power_u_bound a b eps k"
proof -
  have population_positive: "0 < real (power_population a k)"
    using power_population_positive[of a k] by simp
  show ?thesis
    unfolding rz_power_u_exact
    by (rule divide_pos_pos[OF power_learning_rate_positive
          mult_pos_pos[OF eps population_positive]])
qed

lemma rz_power_track_slack_nonnegative:
  assumes beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "0 \<le> rz_power_track_slack a b beta1 eps k"
proof -
  have one_minus_positive: "0 < 1-beta1" using beta1 by linarith
  have denominator_positive: "0 < 2*eps*(1-beta1)"
    using eps one_minus_positive by simp
  have first_nonnegative:
      "0 \<le> beta1 * power_learning_rate b k / (2*eps*(1-beta1))"
    by (rule divide_nonneg_pos)
      (use beta0 power_learning_rate_positive[of b k] denominator_positive in auto)
  have second_nonnegative: "0 \<le> rz_power_u_bound a b eps k / 4"
    using rz_power_u_positive[OF eps, of a b k] by simp
  show ?thesis
    unfolding rz_power_track_slack_def
    using first_nonnegative second_nonnegative by linarith
qed

lemma rz_power_anchor_extra_tendsto_zero:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "((\<lambda>k. real (power_anchor a c k) *
      (power_learning_rate b k/eps) *
      rz_power_track_slack a b beta1 eps k) \<longlongrightarrow> 0) sequentially"
proof -
  let ?eta = "\<lambda>k. power_learning_rate b k"
  let ?N = "\<lambda>k. real (power_population a k)"
  have noise_limit: "((\<lambda>k. (?eta k)^2 * ?N k) \<longlongrightarrow> 0) sequentially"
    by (rule power_law_scaling(2)[OF noise rate tail])
  have pointwise_bounds:
      "0 \<le> real (power_anchor a c k) * (?eta k/eps) *
        rz_power_track_slack a b beta1 eps k \<and>
       real (power_anchor a c k) * (?eta k/eps) *
        rz_power_track_slack a b beta1 eps k \<le>
        (beta1/(2*eps^2*(1-beta1))) * ((?eta k)^2 * ?N k) +
        (?eta k)^2/(4*eps^2)" for k
  proof -
    let ?n = "real (power_anchor a c k)"
    have anchor_le_population: "?n \<le> ?N k"
      using power_counts[OF tail, of k] by simp
    have eta_positive: "0 < ?eta k" by (rule power_learning_rate_positive)
    have population_positive: "0 < ?N k"
      using power_population_positive[of a k] by simp
    have one_minus_positive: "0 < 1-beta1" using beta1 by linarith
    have coefficient_nonnegative: "0 \<le> beta1/(2*eps^2*(1-beta1))"
      by (rule divide_nonneg_pos)
        (use beta0 eps one_minus_positive in auto)
    have eta_square_nonnegative: "0 \<le> (?eta k)^2" by simp
    have weighted_anchor:
        "(?eta k)^2 * ?n \<le> (?eta k)^2 * ?N k"
      by (rule mult_left_mono[OF anchor_le_population eta_square_nonnegative])
    have first_identity:
        "?n*(?eta k/eps)*(beta1*?eta k/(2*eps*(1-beta1))) =
          (beta1/(2*eps^2*(1-beta1)))*((?eta k)^2*?n)"
      using eps one_minus_positive by (simp add: field_simps power2_eq_square; algebra)
    have first_bound:
        "?n*(?eta k/eps)*(beta1*?eta k/(2*eps*(1-beta1))) \<le>
          (beta1/(2*eps^2*(1-beta1)))*((?eta k)^2*?N k)"
      unfolding first_identity
      by (rule mult_left_mono[OF weighted_anchor coefficient_nonnegative])
    have anchor_ratio_nonnegative: "0 \<le> ?n/?N k"
      by (rule divide_nonneg_pos) (use population_positive in simp_all)
    have anchor_ratio_at_most_one: "?n/?N k \<le> 1"
      using anchor_le_population population_positive by (simp add: divide_le_eq)
    have square_scale_nonnegative: "0 \<le> (?eta k)^2/(4*eps^2)"
      by (rule divide_nonneg_pos) (use eps in simp_all)
    have second_identity:
        "?n*(?eta k/eps)*(rz_power_u_bound a b eps k/4) =
          (?n/?N k)*((?eta k)^2/(4*eps^2))"
      unfolding rz_power_u_exact
      using eps population_positive
      by (simp add: field_simps power2_eq_square; algebra)
    have second_bound:
        "?n*(?eta k/eps)*(rz_power_u_bound a b eps k/4) \<le>
          (?eta k)^2/(4*eps^2)"
      unfolding second_identity
      using mult_right_mono[OF anchor_ratio_at_most_one square_scale_nonnegative]
      by simp
    have product_nonnegative:
        "0 \<le> ?n*(?eta k/eps)*rz_power_track_slack a b beta1 eps k"
      by (intro mult_nonneg_nonneg divide_nonneg_nonneg)
        (use eta_positive eps
          rz_power_track_slack_nonnegative[OF beta0 beta1 eps, of a b k] in auto)
    show ?thesis
    proof
      show "0 \<le> ?n*(?eta k/eps)*rz_power_track_slack a b beta1 eps k"
        by (rule product_nonnegative)
      show "?n*(?eta k/eps)*rz_power_track_slack a b beta1 eps k \<le>
          (beta1/(2*eps^2*(1-beta1)))*((?eta k)^2*?N k)+
          (?eta k)^2/(4*eps^2)"
        unfolding rz_power_track_slack_def
        using add_mono[OF first_bound second_bound]
        by (simp add: algebra_simps)
    qed
  qed
  have eta_limit: "(?eta \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have eta_square_limit: "((\<lambda>k. (?eta k)^2) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF eta_limit, of 2] by simp
  have upper_limit: "((\<lambda>k.
      (beta1/(2*eps^2*(1-beta1)))*((?eta k)^2*?N k) +
      (?eta k)^2/(4*eps^2)) \<longlongrightarrow> 0) sequentially"
  proof -
    have first_limit: "((\<lambda>k. (beta1/(2*eps^2*(1-beta1))) *
        ((?eta k)^2*?N k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF tendsto_const noise_limit,
        of "beta1/(2*eps^2*(1-beta1))"] by simp
    have second_limit: "((\<lambda>k. (?eta k)^2/(4*eps^2))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_divide[OF eta_square_limit tendsto_const, of "4*eps^2"] eps
      by simp
    show ?thesis using tendsto_add[OF first_limit second_limit] by simp
  qed
  have lower: "\<forall>\<^sub>F k in sequentially. 0 \<le>
      real (power_anchor a c k)*(?eta k/eps)*
        rz_power_track_slack a b beta1 eps k"
    using pointwise_bounds by (intro always_eventually allI) blast
  have upper: "\<forall>\<^sub>F k in sequentially.
      real (power_anchor a c k)*(?eta k/eps)*
        rz_power_track_slack a b beta1 eps k \<le>
      (beta1/(2*eps^2*(1-beta1)))*((?eta k)^2*?N k)+
        (?eta k)^2/(4*eps^2)"
    using pointwise_bounds by (intro always_eventually allI) blast
  show ?thesis
    by (rule tendsto_sandwich[OF lower upper tendsto_const upper_limit])
qed

lemma rz_power_anchor_over_scale_tendsto_zero:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "((\<lambda>k. rz_power_anchor_bound a b c beta1 eps k /
      real (curriculum_scale k)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  have alpha: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k/eps \<le> 1"
    by (rule rz_power_alpha_eventually_at_most_one[OF noise eps])
  have inverse_scale: "((\<lambda>k. 1/?K k) \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have logarithmic_scale:
      "((\<lambda>k. ln (?K k)/?K k) \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_log_scale_over_scale_tendsto_zero)
  have log_upper_limit:
      "((\<lambda>k. (1+real a*ln (?K k))/?K k)
        \<longlongrightarrow> 0) sequentially"
  proof -
    have scaled_log:
        "((\<lambda>k. real a*(ln (?K k)/?K k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF tendsto_const logarithmic_scale, of "real a"] by simp
    have sum:
        "((\<lambda>k. 1/?K k + real a*(ln (?K k)/?K k))
          \<longlongrightarrow> 0) sequentially"
      using tendsto_add[OF inverse_scale scaled_log] by simp
    show ?thesis using sum
      by (simp add: field_class.field_divide_inverse algebra_simps)
  qed
  have extra: "((\<lambda>k. real (power_anchor a c k)*
      (power_learning_rate b k/eps)*
      rz_power_track_slack a b beta1 eps k) \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_anchor_extra_tendsto_zero[OF noise rate tail beta0 beta1 eps])
  have extra_divided: "((\<lambda>k.
      (real (power_anchor a c k)*(power_learning_rate b k/eps)*
        rz_power_track_slack a b beta1 eps k)/?K k)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have product: "((\<lambda>k.
        (real (power_anchor a c k)*(power_learning_rate b k/eps)*
          rz_power_track_slack a b beta1 eps k) * (1/?K k))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF extra inverse_scale] by simp
    show ?thesis using product
      by (simp add: field_class.field_divide_inverse)
  qed
  have log_nonnegative:
      "0 \<le> ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))" for k
  proof -
    have exponential_nonnegative:
        "0 \<le> exp (power_learning_rate b k/eps)-1"
      using power_learning_rate_positive[of b k] eps by simp
    have product_nonnegative:
        "0 \<le> real (power_anchor a c k)*
          (exp (power_learning_rate b k/eps)-1)"
      by (rule mult_nonneg_nonneg) (use exponential_nonnegative in simp_all)
    have argument_at_least_one:
        "1 \<le> 1+real (power_anchor a c k)*
          (exp (power_learning_rate b k/eps)-1)"
      using product_nonnegative by linarith
    have "ln 1 \<le> ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))"
      by (rule ln_mono[OF argument_at_least_one]) simp
    then show ?thesis by simp
  qed
  have lower: "\<forall>\<^sub>F k in sequentially. 0 \<le>
      ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))/?K k"
    by (intro always_eventually allI divide_nonneg_nonneg log_nonnegative) simp
  have upper: "\<forall>\<^sub>F k in sequentially.
      ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))/?K k \<le>
      (1+real a*ln (?K k))/?K k"
  proof (rule eventually_mono[OF alpha])
    fix k
    assume alpha_at_most_one: "power_learning_rate b k/eps \<le> 1"
    have scale_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have logarithm_upper:
        "ln (1+real (power_anchor a c k)*
          (exp (power_learning_rate b k/eps)-1)) \<le>
         1+real a*ln (?K k)"
      by (rule rz_power_anchor_log_upper[OF tail alpha_at_most_one eps])
    show "ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))/?K k \<le>
      (1+real a*ln (?K k))/?K k"
      by (rule divide_right_mono[OF logarithm_upper])
        (use scale_positive in linarith)
  qed
  have logarithm_limit: "((\<lambda>k.
      ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))/?K k)
      \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[OF lower upper tendsto_const log_upper_limit])
  have total: "((\<lambda>k.
      ln (1+real (power_anchor a c k)*
        (exp (power_learning_rate b k/eps)-1))/?K k +
      (real (power_anchor a c k)*(power_learning_rate b k/eps)*
        rz_power_track_slack a b beta1 eps k)/?K k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF logarithm_limit extra_divided] by simp
  show ?thesis using total
    by (simp add: rz_power_anchor_bound_def add_divide_distrib)
qed

section \<open>Eventual finite certificates\<close>

lemma rz_power_finite_side_conditions:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    power_learning_rate b k*decay \<le> 1/2 \<and>
    power_learning_rate b k/eps \<le> 1 \<and>
    rz_power_u_bound a b eps k \<le> 1 \<and>
    power_tail c k \<ge> rz_burn_index beta1 + 3"
proof -
  have learning_rate_limit:
      "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have decay_eventually:
      "\<forall>\<^sub>F k in sequentially. power_learning_rate b k*decay < 1/2"
  proof (cases "decay = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have decay_positive: "0 < decay" using decay False by linarith
    have limit: "((\<lambda>k. power_learning_rate b k*decay)
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF learning_rate_limit tendsto_const] by simp
    show ?thesis using order_tendstoD(2)[OF limit, of "1/2"] by simp
  qed
  have alpha: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k/eps \<le> 1"
    by (rule rz_power_alpha_eventually_at_most_one[OF noise eps])
  have auxiliary_limit:
      "((\<lambda>k. rz_power_u_bound a b eps k) \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_u_tendsto_zero[OF noise tail eps])
  have auxiliary_eventually:
      "\<forall>\<^sub>F k in sequentially. rz_power_u_bound a b eps k < 1"
    using order_tendstoD(2)[OF auxiliary_limit, of 1] by simp
  let ?J = "rz_burn_index beta1"
  have tail_large: "\<forall>\<^sub>F k in sequentially. ?J+3 \<le> power_tail c k"
  proof -
    have c_positive: "0 < c" using rate by arith
    show ?thesis
      unfolding eventually_sequentially
    proof (intro exI[of _ "?J+3"] allI impI)
      fix k
      assume index: "?J+3 \<le> k"
      have index_le_scale: "k \<le> curriculum_scale k"
        unfolding curriculum_scale_def by arith
      have scale_at_least_one: "1 \<le> curriculum_scale k"
        using curriculum_scale_at_least_four[of k] by simp
      have scale_le_power:
          "curriculum_scale k \<le> curriculum_scale k ^ c"
      proof -
        obtain d where c_successor: "c = Suc d"
          using c_positive by (cases c) auto
        have "1 \<le> curriculum_scale k ^ d"
          by (rule one_le_power[OF scale_at_least_one])
        then show ?thesis unfolding c_successor power_Suc by simp
      qed
      show "?J+3 \<le> power_tail c k"
        unfolding power_tail_def using index index_le_scale scale_le_power by arith
    qed
  qed
note combined = eventually_conj[OF decay_eventually
    eventually_conj[OF alpha
      eventually_conj[OF auxiliary_eventually tail_large]]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume conditions:
      "power_learning_rate b k*decay < 1/2 \<and>
       power_learning_rate b k/eps \<le> 1 \<and>
       rz_power_u_bound a b eps k < 1 \<and>
       ?J+3 \<le> power_tail c k"
    show "power_learning_rate b k*decay \<le> 1/2 \<and>
      power_learning_rate b k/eps \<le> 1 \<and>
      rz_power_u_bound a b eps k \<le> 1 \<and>
      ?J+3 \<le> power_tail c k"
      using conditions by linarith
  qed
qed

lemma rz_power_takeover_eventually:
  fixes r :: nat
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1" and eps: "0 < eps"
  shows "\<forall>\<^sub>F k in sequentially.
    rz_burn_index beta1 + r \<le> power_tail c k \<and>
    rz_power_anchor_bound a b c beta1 eps k +
      real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
      real (power_tail c k-r-rz_burn_index beta1) *
        (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?J = "rz_burn_index beta1"
  let ?d = "rz_tail_floor/(2*(1+eps))"
  have drift_positive: "0 < ?d"
    by (rule divide_pos_pos)
      (use rz_tail_floor_positive eps in auto)
  have anchor_limit: "((\<lambda>k.
      rz_power_anchor_bound a b c beta1 eps k/?K k)
      \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_anchor_over_scale_tendsto_zero
        [OF noise rate tail beta0 beta1 eps])
  have learning_rate_limit:
      "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have inverse_scale: "((\<lambda>k. 1/?K k) \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have burn_limit: "((\<lambda>k.
      real ?J*(2*power_learning_rate b k/eps)/?K k)
      \<longlongrightarrow> 0) sequentially"
  proof -
have scaled_learning_rate: "((\<lambda>k. (2/eps)*power_learning_rate b k)
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF tendsto_const learning_rate_limit, of "2/eps"]
      by simp
    have numerator: "((\<lambda>k.
        real ?J*(2*power_learning_rate b k/eps))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF tendsto_const scaled_learning_rate, of "real ?J"]
      by (simp add: algebra_simps)    have product: "((\<lambda>k.
        (real ?J*(2*power_learning_rate b k/eps))*(1/?K k))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF numerator inverse_scale] by simp
    show ?thesis using product
      by (simp add: field_class.field_divide_inverse)
  qed
  have small_sum_limit: "((\<lambda>k.
      rz_power_anchor_bound a b c beta1 eps k/?K k +
      real ?J*(2*power_learning_rate b k/eps)/?K k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF anchor_limit burn_limit] by simp
have half_drift_positive: "0 < ?d/2"
    by (rule divide_pos_pos[OF drift_positive]) simp
  have small_sum: "\<forall>\<^sub>F k in sequentially.
      rz_power_anchor_bound a b c beta1 eps k/?K k +
      real ?J*(2*power_learning_rate b k/eps)/?K k < ?d/2"
    using order_tendstoD(2)[OF small_sum_limit half_drift_positive] by simp  have eta_over_scale: "((\<lambda>k. power_learning_rate b k/?K k)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have product: "((\<lambda>k.
        power_learning_rate b k*(1/?K k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF learning_rate_limit inverse_scale] by simp
    show ?thesis using product
      by (simp add: field_class.field_divide_inverse)
  qed
  have removed_small: "\<forall>\<^sub>F k in sequentially.
      real (r+?J)*power_learning_rate b k/?K k < 1/2"
  proof -
    have limit: "((\<lambda>k.
        real (r+?J)*(power_learning_rate b k/?K k))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_mult[OF tendsto_const eta_over_scale, of "real (r+?J)"]
      by simp
    show ?thesis using order_tendstoD(2)[OF limit, of "1/2"] by simp
  qed
  have tail_large: "\<forall>\<^sub>F k in sequentially. ?J+r \<le> power_tail c k"
  proof -
    have c_positive: "0 < c" using rate by arith
    show ?thesis
      unfolding eventually_sequentially
    proof (intro exI[of _ "?J+r"] allI impI)
      fix k
      assume index: "?J+r \<le> k"
      have index_le_scale: "k \<le> curriculum_scale k"
        unfolding curriculum_scale_def by arith
      have scale_at_least_one: "1 \<le> curriculum_scale k"
        using curriculum_scale_at_least_four[of k] by simp
      have scale_le_power:
          "curriculum_scale k \<le> curriculum_scale k ^ c"
      proof -
        obtain d where c_successor: "c = Suc d"
          using c_positive by (cases c) auto
        have "1 \<le> curriculum_scale k ^ d"
          by (rule one_le_power[OF scale_at_least_one])
        then show ?thesis unfolding c_successor power_Suc by simp
      qed
      show "?J+r \<le> power_tail c k"
        unfolding power_tail_def using index index_le_scale scale_le_power by arith
    qed
  qed
  note combined = eventually_conj[OF small_sum
    eventually_conj[OF removed_small tail_large]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume conditions:
      "rz_power_anchor_bound a b c beta1 eps k/?K k +
         real ?J*(2*power_learning_rate b k/eps)/?K k < ?d/2 \<and>
       real (r+?J)*power_learning_rate b k/?K k < 1/2 \<and>
       ?J+r \<le> power_tail c k"
    from conditions have small_condition:
        "rz_power_anchor_bound a b c beta1 eps k/?K k +
          real ?J*(2*power_learning_rate b k/eps)/?K k < ?d/2"
      and removed_condition:
        "real (r+?J)*power_learning_rate b k/?K k < 1/2"
      and tail_condition: "?J+r \<le> power_tail c k"
      by auto
    have scale_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have mass: "?K k \<le>
        power_learning_rate b k*real (power_tail c k)"
      by (rule power_effective_tail_mass_at_least_scale[OF rate])
    have remaining_mass: "?K k/2 \<le>
        power_learning_rate b k*real (power_tail c k-r-?J)"
    proof -
      have cast_remaining: "real (power_tail c k-r-?J) =
          real (power_tail c k)-real (r+?J)"
using tail_condition by simp
      have removed: "real (r+?J)*power_learning_rate b k < ?K k/2"
        using removed_condition scale_positive
        by (simp add: pos_divide_less_eq)      have difference_lower:
          "?K k/2 <
            power_learning_rate b k*real (power_tail c k) -
            real (r+?J)*power_learning_rate b k"
        using mass removed by linarith
      have remaining_identity:
          "power_learning_rate b k*real (power_tail c k-r-?J) =
           power_learning_rate b k*real (power_tail c k) -
           real (r+?J)*power_learning_rate b k"
        unfolding cast_remaining by algebra
      show ?thesis unfolding remaining_identity using difference_lower by linarith
    qed
have divided_left:
        "(rz_power_anchor_bound a b c beta1 eps k +
          real ?J*(2*power_learning_rate b k/eps))/?K k < ?d/2"
      using small_condition by (simp add: add_divide_distrib)
    have left:
        "rz_power_anchor_bound a b c beta1 eps k +
         real ?J*(2*power_learning_rate b k/eps) < (?d/2)*?K k"
      using divided_left scale_positive by (simp add: pos_divide_less_eq)
    have scaled_remaining:
        "(?K k/2)*?d \<le>
         (power_learning_rate b k*real (power_tail c k-r-?J))*?d"
      by (rule mult_right_mono[OF remaining_mass])
        (use drift_positive in linarith)
have left_threshold_identity:
        "(?d/2)*?K k = (?K k/2)*?d"
      by (simp add: divide_simps; algebra)
    have right_product_identity:
        "(power_learning_rate b k*real (power_tail c k-r-?J))*?d =
         real (power_tail c k-r-?J)*(power_learning_rate b k*?d)"
      by algebra
have right: "(?d/2)*?K k \<le>
        real (power_tail c k-r-?J)*(power_learning_rate b k*?d)"
    proof -
      have "(?d/2)*?K k = (?K k/2)*?d"
        by (rule left_threshold_identity)
      also have "... \<le>
          (power_learning_rate b k*real (power_tail c k-r-?J))*?d"
        by (rule scaled_remaining)
      also have "... =
          real (power_tail c k-r-?J)*(power_learning_rate b k*?d)"
        by (rule right_product_identity)
      finally show ?thesis .
    qed
    show "?J+r \<le> power_tail c k \<and>
      rz_power_anchor_bound a b c beta1 eps k +
        real ?J*(2*power_learning_rate b k/eps) -
        real (power_tail c k-r-?J)*
          (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0"
    proof
      show "?J+r \<le> power_tail c k" using conditions by simp
      show "rz_power_anchor_bound a b c beta1 eps k +
          real ?J*(2*power_learning_rate b k/eps) -
          real (power_tail c k-r-?J)*
            (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0"
        using left right
        by (simp add: algebra_simps; linarith)
    qed
  qed
qed

lemma rz_power_random_conditions_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    0 \<le> rz_power_drift_coeff a b c beta1 eps decay k \<and>
    rz_power_u_bound a b eps k <
      rz_safe_delta eps decay - 2*power_learning_rate b k/eps -
        rz_power_drift_error a b beta1 eps k \<and>
    rz_power_u_bound a b eps k <
      power_learning_rate b k *
        rz_power_drift_coeff a b c beta1 eps decay k *
        real (power_population a k) -
      rz_power_drift_error a b beta1 eps k"
proof -
  let ?q = "sigmoid (-1)"
  let ?c0 = "?q/(2*(1+eps))"
  have c0_positive: "0 < ?c0"
    by (rule divide_pos_pos)
      (use sigmoid_pos[of "-1"] eps in auto)
  have coefficient: "\<forall>\<^sub>F k in sequentially. ?c0 \<le>
      rz_power_drift_coeff a b c beta1 eps decay k"
    by (rule rz_power_drift_coeff_eventually_positive
        [OF noise tail beta0 beta1 eps decay])
  have auxiliary_limit:
      "((\<lambda>k. rz_power_u_bound a b eps k) \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_u_tendsto_zero[OF noise tail eps])
  have learning_rate_limit:
      "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have scaled_rate_limit:
      "((\<lambda>k. 2*power_learning_rate b k/eps)
        \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const learning_rate_limit, of "2/eps"]
    by (simp add: algebra_simps)
  have drift_error_limit:
      "((\<lambda>k. rz_power_drift_error a b beta1 eps k)
        \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_drift_error_tendsto_zero[OF noise beta0 beta1 eps])
  have landing_error_limit: "((\<lambda>k.
      rz_power_u_bound a b eps k + 2*power_learning_rate b k/eps +
      rz_power_drift_error a b beta1 eps k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF tendsto_add[OF auxiliary_limit scaled_rate_limit]
      drift_error_limit]
    by simp
  have delta_positive: "0 < rz_safe_delta eps decay"
    by (rule rz_safe_delta_positive[OF eps decay])
  have landing: "\<forall>\<^sub>F k in sequentially.
      rz_power_u_bound a b eps k + 2*power_learning_rate b k/eps +
      rz_power_drift_error a b beta1 eps k < rz_safe_delta eps decay"
    using order_tendstoD(2)[OF landing_error_limit delta_positive] by simp
  have total_error_limit: "((\<lambda>k.
      rz_power_u_bound a b eps k +
      rz_power_drift_error a b beta1 eps k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF auxiliary_limit drift_error_limit] by simp
  have four_c0_positive: "0 < 4*?c0" using c0_positive by simp
  have small: "\<forall>\<^sub>F k in sequentially.
      rz_power_u_bound a b eps k +
      rz_power_drift_error a b beta1 eps k < 4*?c0"
    using order_tendstoD(2)[OF total_error_limit four_c0_positive] by simp
  note combined = eventually_conj[OF coefficient
    eventually_conj[OF landing small]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume conditions:
      "?c0 \<le> rz_power_drift_coeff a b c beta1 eps decay k \<and>
       rz_power_u_bound a b eps k + 2*power_learning_rate b k/eps +
         rz_power_drift_error a b beta1 eps k < rz_safe_delta eps decay \<and>
       rz_power_u_bound a b eps k +
         rz_power_drift_error a b beta1 eps k < 4*?c0"
    from conditions have coefficient_lower:
        "?c0 \<le> rz_power_drift_coeff a b c beta1 eps decay k"
      and landing_condition:
        "rz_power_u_bound a b eps k + 2*power_learning_rate b k/eps +
          rz_power_drift_error a b beta1 eps k < rz_safe_delta eps decay"
      and small_condition:
        "rz_power_u_bound a b eps k +
          rz_power_drift_error a b beta1 eps k < 4*?c0"
      by auto
    have mass: "real (curriculum_scale k) \<le>
        power_learning_rate b k*real (power_tail c k)"
      by (rule power_effective_tail_mass_at_least_scale[OF rate])
    have tail_le_population:
        "power_tail c k \<le> power_population a k"
      by (rule power_tail_le_population[OF tail])
    have rate_nonnegative: "0 \<le> power_learning_rate b k"
      using power_learning_rate_positive[of b k] by linarith
    have tail_mass_le_population_mass:
        "power_learning_rate b k*real (power_tail c k) \<le>
         power_learning_rate b k*real (power_population a k)"
      by (rule mult_left_mono[OF of_nat_mono[OF tail_le_population]
            rate_nonnegative])
    have population_mass:
        "real (curriculum_scale k) \<le>
         power_learning_rate b k*real (power_population a k)"
      by (rule order_trans[OF mass tail_mass_le_population_mass])
    have scale_at_least_four: "4 \<le> real (curriculum_scale k)"
      using curriculum_scale_at_least_four[of k] by simp
    have scale_c0:
        "4*?c0 \<le> real (curriculum_scale k)*?c0"
      by (rule mult_right_mono[OF scale_at_least_four])
        (use c0_positive in linarith)
    have mass_c0:
        "real (curriculum_scale k)*?c0 \<le>
         (power_learning_rate b k*real (power_population a k))*?c0"
      by (rule mult_right_mono[OF population_mass])
        (use c0_positive in linarith)
    have mass_nonnegative:
        "0 \<le> power_learning_rate b k*real (power_population a k)"
      by (rule mult_nonneg_nonneg) (use rate_nonnegative in simp_all)
    have coefficient_c0:
        "(power_learning_rate b k*real (power_population a k))*?c0 \<le>
         (power_learning_rate b k*real (power_population a k))*
           rz_power_drift_coeff a b c beta1 eps decay k"
      by (rule mult_left_mono[OF coefficient_lower mass_nonnegative])
    have lower_chain:
        "4*?c0 \<le>
         (power_learning_rate b k*real (power_population a k))*
           rz_power_drift_coeff a b c beta1 eps decay k"
      by (rule order_trans[OF scale_c0
            order_trans[OF mass_c0 coefficient_c0]])
    have product_identity:
        "(power_learning_rate b k*real (power_population a k))*
           rz_power_drift_coeff a b c beta1 eps decay k =
         power_learning_rate b k*
           rz_power_drift_coeff a b c beta1 eps decay k*
           real (power_population a k)"
      by algebra
    have total_lower: "4*?c0 \<le>
        power_learning_rate b k*
          rz_power_drift_coeff a b c beta1 eps decay k*
          real (power_population a k)"
      unfolding product_identity[symmetric] by (rule lower_chain)
    show "0 \<le> rz_power_drift_coeff a b c beta1 eps decay k \<and>
      rz_power_u_bound a b eps k <
        rz_safe_delta eps decay - 2*power_learning_rate b k/eps -
          rz_power_drift_error a b beta1 eps k \<and>
      rz_power_u_bound a b eps k <
        power_learning_rate b k*
          rz_power_drift_coeff a b c beta1 eps decay k*
          real (power_population a k) -
        rz_power_drift_error a b beta1 eps k"
      using coefficient_lower landing_condition small_condition total_lower c0_positive
      by (intro conjI; linarith)
  qed
qed

section \<open>Exact power-law random metric\<close>

definition rz_power_random_metric_event ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    real \<Rightarrow> nat \<Rightarrow> bool list set" where
  "rz_power_random_metric_event a b c beta1 beta2 eps decay k = {xs.
    realizable_test_risk (power_tail_ratio a c k)
      (aw_weight (fst (rz_run (power_learning_rate b k) beta1 beta2 eps decay
        (rz_power_kappa a k) (\<lambda>i. xs ! i) (power_population a k))))
      (rz_power_kappa a k *
        aw_weight (snd (rz_run (power_learning_rate b k) beta1 beta2 eps decay
          (rz_power_kappa a k) (\<lambda>i. xs ! i) (power_population a k)))) =
      power_tail_ratio a c k \<and>
    realizable_test_auc (power_tail_ratio a c k)
      (aw_weight (fst (rz_run (power_learning_rate b k) beta1 beta2 eps decay
        (rz_power_kappa a k) (\<lambda>i. xs ! i) (power_population a k))))
      (rz_power_kappa a k *
        aw_weight (snd (rz_run (power_learning_rate b k) beta1 beta2 eps decay
          (rz_power_kappa a k) (\<lambda>i. xs ! i) (power_population a k)))) =
      1-(power_tail_ratio a c k)^2}"

definition rz_power_random_benign_probability ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_random_benign_probability a b c beta1 beta2 eps decay k =
    uniform_probability
      (binary_orders (power_anchor a c k) (power_population a k))
      (rz_power_random_metric_event a b c beta1 beta2 eps decay k)"

lemma rz_power_random_probability_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    1-power_confidence k \<le>
      rz_power_random_benign_probability a b c beta1 beta2 eps decay k"
proof -
  have side: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k*decay \<le> 1/2 \<and>
      power_learning_rate b k/eps \<le> 1 \<and>
      rz_power_u_bound a b eps k \<le> 1 \<and>
      rz_burn_index beta1+3 \<le> power_tail c k"
    by (rule rz_power_finite_side_conditions
        [OF noise rate tail beta10 beta11 eps decay])
  have conditions: "\<forall>\<^sub>F k in sequentially.
    0 \<le> rz_power_drift_coeff a b c beta1 eps decay k \<and>
    rz_power_u_bound a b eps k < rz_safe_delta eps decay -
      2*power_learning_rate b k/eps -
      rz_power_drift_error a b beta1 eps k \<and>
    rz_power_u_bound a b eps k <
      power_learning_rate b k*
        rz_power_drift_coeff a b c beta1 eps decay k*
        real (power_population a k) -
      rz_power_drift_error a b beta1 eps k"
    by (rule rz_power_random_conditions_eventually
        [OF noise rate tail beta10 beta11 eps decay])
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF side conditions]])
    fix k
    assume assumptions:
      "(power_learning_rate b k*decay \<le> 1/2 \<and>
        power_learning_rate b k/eps \<le> 1 \<and>
        rz_power_u_bound a b eps k \<le> 1 \<and>
        rz_burn_index beta1+3 \<le> power_tail c k) \<and>
       0 \<le> rz_power_drift_coeff a b c beta1 eps decay k \<and>
       rz_power_u_bound a b eps k < rz_safe_delta eps decay -
         2*power_learning_rate b k/eps -
         rz_power_drift_error a b beta1 eps k \<and>
       rz_power_u_bound a b eps k <
         power_learning_rate b k*
           rz_power_drift_coeff a b c beta1 eps decay k*
           real (power_population a k) -
         rz_power_drift_error a b beta1 eps k"
    let ?N = "power_population a k"
    let ?n = "power_anchor a c k"
    let ?eta = "power_learning_rate b k"
    let ?kappa = "rz_power_kappa a k"
    have counts: "power_tail c k + ?n = ?N"
      by (rule power_counts[OF tail])
    have sample: "?n \<le> ?N" using counts by arith
    have population_positive: "0 < ?N" by (rule power_population_positive)
    have learning_rate_positive: "0 < ?eta"
      by (rule power_learning_rate_positive)
    have kappa_positive: "0 < ?kappa" by (rule rz_power_kappa_positive)
    have decay_step: "?eta*decay \<le> 1" using assumptions by linarith
    interpret opt: rz_parameters ?eta beta1 beta2 eps decay ?kappa
      by unfold_locales
        (use learning_rate_positive beta10 beta11 beta20 beta21 eps decay
          decay_step kappa_positive in auto)
    have anchor_fraction:
        "real ?n/real ?N = 1-power_tail_ratio a c k"
    proof -
      have population_real_positive: "0 < real ?N"
        using population_positive by simp
      have cast_counts:
          "real (power_tail c k)+real ?n = real ?N"
        using counts by simp
      show ?thesis
        unfolding power_tail_ratio_def
        using population_real_positive cast_counts
        by (simp add: field_simps; algebra)
    qed
    have radius_identity: "rz_power_prefix_radius a k =
        sqrt (real ?N/2*ln (2*real ?N/power_confidence k))"
      by (simp add: rz_power_prefix_radius_def)
    have track_identity:
        "opt.Slack ?N = rz_power_track_slack a b beta1 eps k"
      unfolding rz_power_track_slack_def rz_power_u_bound_def
      by (simp add: algebra_simps)
    have tail_complement:
        "1-real ?n/real ?N = power_tail_ratio a c k"
      using anchor_fraction by linarith
    have drift_identity:
        "opt.Abenign (rz_safe_delta eps decay) (real ?n/real ?N) ?N =
         ?eta*rz_power_drift_coeff a b c beta1 eps decay k"
    proof -
      have expanded: "opt.Abenign (rz_safe_delta eps decay)
          (real ?n/real ?N) ?N = ?eta *
        (sigmoid (-rz_safe_delta eps decay)/(1+eps) -
         decay*rz_safe_delta eps decay - opt.Slack ?N/eps -
         (1-real ?n/real ?N)/eps)"
        by (simp add: algebra_simps)
      show ?thesis
        using expanded tail_complement track_identity
        unfolding rz_power_drift_coeff_def by simp
    qed
    have error_identity:
        "opt.Ebenign (rz_power_prefix_radius a k) =
         rz_power_drift_error a b beta1 eps k"
      unfolding rz_power_drift_error_def
      by (simp add: algebra_simps)
    have auxiliary_identity:
        "opt.UB ?N = rz_power_u_bound a b eps k"
      unfolding rz_power_u_bound_def
      by (simp add: algebra_simps)
    have drift_nonnegative:
        "0 \<le> opt.Abenign (rz_safe_delta eps decay)
          (real ?n/real ?N) ?N"
      using drift_identity learning_rate_positive assumptions by auto
    have landing_condition:
        "opt.UB ?N < rz_safe_delta eps decay - 2 * ?eta/eps -
          opt.Ebenign
            (sqrt (real ?N/2*ln (2*real ?N/power_confidence k)))"
      using assumptions auxiliary_identity error_identity radius_identity by simp
    have total_condition:
        "opt.UB ?N <
          opt.Abenign (rz_safe_delta eps decay) (real ?n/real ?N) ?N *
            real ?N -
          opt.Ebenign
            (sqrt (real ?N/2*ln (2*real ?N/power_confidence k)))"
      using assumptions auxiliary_identity error_identity radius_identity
        drift_identity
      by (simp add: mult.commute mult.left_commute)
    have probability: "1-power_confidence k \<le>
      uniform_probability (binary_orders ?n ?N)
        {xs. realizable_test_risk (power_tail_ratio a c k)
            (opt.A (\<lambda>i. xs ! i) ?N)
            (opt.Uc (\<lambda>i. xs ! i) ?N) = power_tail_ratio a c k \<and>
          realizable_test_auc (power_tail_ratio a c k)
            (opt.A (\<lambda>i. xs ! i) ?N)
            (opt.Uc (\<lambda>i. xs ! i) ?N) =
              1-(power_tail_ratio a c k)^2}"
      by (rule opt.rz_random_order_benign_probability
        [OF population_positive sample power_confidence_positive[of k]
          power_confidence_at_most_one[of k] drift_nonnegative
          landing_condition total_condition,
         where epsilon="power_tail_ratio a c k"])
    have event_identity:
        "{xs. realizable_test_risk (power_tail_ratio a c k)
            (opt.A (\<lambda>i. xs ! i) ?N)
            (opt.Uc (\<lambda>i. xs ! i) ?N) = power_tail_ratio a c k \<and>
          realizable_test_auc (power_tail_ratio a c k)
            (opt.A (\<lambda>i. xs ! i) ?N)
            (opt.Uc (\<lambda>i. xs ! i) ?N) =
              1-(power_tail_ratio a c k)^2} =
         rz_power_random_metric_event a b c beta1 beta2 eps decay k"
      unfolding rz_power_random_metric_event_def
      by (rule refl)
    show "1-power_confidence k \<le>
      rz_power_random_benign_probability a b c beta1 beta2 eps decay k"
      using probability event_identity
      unfolding rz_power_random_benign_probability_def by simp
  qed
qed

theorem rz_power_random_probability_tendsto_one:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "((\<lambda>k. rz_power_random_benign_probability
      a b c beta1 beta2 eps decay k) \<longlongrightarrow> 1) sequentially"
proof -
  have lower_limit: "((\<lambda>k. 1-power_confidence k) \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const power_confidence_tendsto_zero] by simp
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 1-power_confidence k \<le>
      rz_power_random_benign_probability a b c beta1 beta2 eps decay k"
    by (rule rz_power_random_probability_eventually[OF noise rate tail beta10
          beta11 beta20 beta21 eps decay])
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      rz_power_random_benign_probability a b c beta1 beta2 eps decay k \<le> 1"
    by (intro always_eventually allI)
      (simp add: rz_power_random_benign_probability_def
        uniform_probability_le_one[OF finite_binary_orders])
  show ?thesis
    by (rule tendsto_sandwich[OF lower_bound upper_bound lower_limit tendsto_const])
qed


section \<open>Exact power-law attack metric\<close>

definition rz_power_attack_main ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_attack_main a b c beta1 beta2 eps decay k =
    aw_weight (fst (rz_run (power_learning_rate b k) beta1 beta2 eps decay
      (rz_power_kappa a k)
      (\<lambda>i. attack_order (power_anchor a c k) (power_tail c k) ! i)
      (power_population a k)))"

definition rz_power_attack_aux ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "rz_power_attack_aux a b c beta1 beta2 eps decay k =
    rz_power_kappa a k *
      aw_weight (snd (rz_run (power_learning_rate b k) beta1 beta2 eps decay
        (rz_power_kappa a k)
        (\<lambda>i. attack_order (power_anchor a c k) (power_tail c k) ! i)
        (power_population a k)))"

lemma rz_power_attack_conditions_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta0: "0 \<le> beta1" and beta1: "beta1 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    power_learning_rate b k*decay \<le> 1/2 \<and>
    power_learning_rate b k/eps \<le> 1 \<and>
    rz_power_u_bound a b eps k \<le> 1 \<and>
    rz_burn_index beta1+1 \<le> power_tail c k \<and>
    rz_power_anchor_bound a b c beta1 eps k +
      real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
      real (power_tail c k-1-rz_burn_index beta1) *
        (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0 \<and>
    power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2 \<and>
    rz_power_u_bound a b eps k <
      power_learning_rate b k*rz_terminal_rate beta1 eps"
proof -
  have side: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k*decay \<le> 1/2 \<and>
      power_learning_rate b k/eps \<le> 1 \<and>
      rz_power_u_bound a b eps k \<le> 1 \<and>
      rz_burn_index beta1+3 \<le> power_tail c k"
    by (rule rz_power_finite_side_conditions
        [OF noise rate tail beta0 beta1 eps decay])
  have takeover: "\<forall>\<^sub>F k in sequentially.
      rz_burn_index beta1+1 \<le> power_tail c k \<and>
      rz_power_anchor_bound a b c beta1 eps k +
        real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
        real (power_tail c k-1-rz_burn_index beta1) *
          (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0"
    by (rule rz_power_takeover_eventually
        [OF noise rate tail beta0 beta1 eps, where r=1])
  have terminal_positive: "0 < rz_terminal_rate beta1 eps"
    by (rule rz_terminal_rate_positive[OF beta0 beta1 eps])
  have learning_rate_limit:
      "((\<lambda>k. power_learning_rate b k) \<longlongrightarrow> 0) sequentially"
    by (rule power_learning_rate_tendsto_zero[OF noise])
  have terminal_limit: "((\<lambda>k.
      power_learning_rate b k*rz_terminal_rate beta1 eps)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF learning_rate_limit tendsto_const] by simp
  have terminal_strict: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k*rz_terminal_rate beta1 eps < 1/2"
    using order_tendstoD(2)[OF terminal_limit, of "1/2"] by simp
  have terminal_small: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2"
    using terminal_strict by eventually_elim linarith
  have ratio_limit: "((\<lambda>k.
      rz_power_u_bound a b eps k / power_learning_rate b k)
      \<longlongrightarrow> 0) sequentially"
    by (rule rz_power_u_over_eta_tendsto_zero[OF tail eps])
  have ratio_small: "\<forall>\<^sub>F k in sequentially.
      rz_power_u_bound a b eps k / power_learning_rate b k <
        rz_terminal_rate beta1 eps"
    using order_tendstoD(2)[OF ratio_limit terminal_positive] by simp
  have auxiliary_dominated: "\<forall>\<^sub>F k in sequentially.
      rz_power_u_bound a b eps k <
        power_learning_rate b k*rz_terminal_rate beta1 eps"
  proof (rule eventually_mono[OF ratio_small])
    fix k
    assume small: "rz_power_u_bound a b eps k / power_learning_rate b k <
      rz_terminal_rate beta1 eps"
    have eta_positive: "0 < power_learning_rate b k"
      by (rule power_learning_rate_positive)
    have scaled: "(rz_power_u_bound a b eps k / power_learning_rate b k) *
        power_learning_rate b k <
      rz_terminal_rate beta1 eps * power_learning_rate b k"
      by (rule mult_strict_right_mono[OF small eta_positive])
    show "rz_power_u_bound a b eps k <
      power_learning_rate b k*rz_terminal_rate beta1 eps"
      using scaled eta_positive by (simp add: mult.commute)
  qed
  note combined = eventually_conj[OF side
    eventually_conj[OF takeover
      eventually_conj[OF terminal_small auxiliary_dominated]]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume conditions:
      "(power_learning_rate b k*decay \<le> 1/2 \<and>
        power_learning_rate b k/eps \<le> 1 \<and>
        rz_power_u_bound a b eps k \<le> 1 \<and>
        rz_burn_index beta1+3 \<le> power_tail c k) \<and>
       (rz_burn_index beta1+1 \<le> power_tail c k \<and>
        rz_power_anchor_bound a b c beta1 eps k +
          real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
          real (power_tail c k-1-rz_burn_index beta1) *
            (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0) \<and>
       power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2 \<and>
       rz_power_u_bound a b eps k <
         power_learning_rate b k*rz_terminal_rate beta1 eps"
    show "power_learning_rate b k*decay \<le> 1/2 \<and>
      power_learning_rate b k/eps \<le> 1 \<and>
      rz_power_u_bound a b eps k \<le> 1 \<and>
      rz_burn_index beta1+1 \<le> power_tail c k \<and>
      rz_power_anchor_bound a b c beta1 eps k +
        real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
        real (power_tail c k-1-rz_burn_index beta1) *
          (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0 \<and>
      power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2 \<and>
      rz_power_u_bound a b eps k <
        power_learning_rate b k*rz_terminal_rate beta1 eps"
      using conditions by blast
  qed
qed


theorem rz_power_attack_dominance_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    rz_power_attack_main a b c beta1 beta2 eps decay k <
      - rz_power_attack_aux a b c beta1 beta2 eps decay k"
proof -
  have conditions: "\<forall>\<^sub>F k in sequentially.
    power_learning_rate b k*decay \<le> 1/2 \<and>
    power_learning_rate b k/eps \<le> 1 \<and>
    rz_power_u_bound a b eps k \<le> 1 \<and>
    rz_burn_index beta1+1 \<le> power_tail c k \<and>
    rz_power_anchor_bound a b c beta1 eps k +
      real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
      real (power_tail c k-1-rz_burn_index beta1) *
        (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0 \<and>
    power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2 \<and>
    rz_power_u_bound a b eps k <
      power_learning_rate b k*rz_terminal_rate beta1 eps"
    by (rule rz_power_attack_conditions_eventually
        [OF noise rate tail beta10 beta11 eps decay])
  show ?thesis
  proof (rule eventually_mono[OF conditions])
    fix k
    assume assumptions:
      "power_learning_rate b k*decay \<le> 1/2 \<and>
       power_learning_rate b k/eps \<le> 1 \<and>
       rz_power_u_bound a b eps k \<le> 1 \<and>
       rz_burn_index beta1+1 \<le> power_tail c k \<and>
       rz_power_anchor_bound a b c beta1 eps k +
         real (rz_burn_index beta1)*(2*power_learning_rate b k/eps) -
         real (power_tail c k-1-rz_burn_index beta1) *
           (power_learning_rate b k*rz_tail_floor/(2*(1+eps))) < 0 \<and>
       power_learning_rate b k*rz_terminal_rate beta1 eps \<le> 1/2 \<and>
       rz_power_u_bound a b eps k <
         power_learning_rate b k*rz_terminal_rate beta1 eps"
    let ?n = "power_anchor a c k"
    let ?m = "power_tail c k"
    let ?N = "power_population a k"
    let ?eta = "power_learning_rate b k"
    let ?kappa = "rz_power_kappa a k"
    let ?xs = "\<lambda>i. attack_order ?n ?m ! i"
    have counts: "?n+?m = ?N"
      using power_counts[OF tail, of k] by arith
    have sample: "?n \<le> ?N" using counts by arith
    have population_positive: "0 < ?N" by (rule power_population_positive)
    have tail_positive: "0 < ?m" by (rule power_tail_positive)
    have learning_rate_positive: "0 < ?eta"
      by (rule power_learning_rate_positive)
    have kappa_positive: "0 < ?kappa" by (rule rz_power_kappa_positive)
    have decay_step: "?eta*decay \<le> 1" using assumptions by linarith
    interpret opt: rz_parameters ?eta beta1 beta2 eps decay ?kappa
      by unfold_locales
        (use learning_rate_positive beta10 beta11 beta20 beta21 eps decay
          decay_step kappa_positive in auto)
    have anchor_order: "\<And>i. i < ?n \<Longrightarrow> ?xs i"
    proof -
      fix i
      assume i_less: "i < ?n"
      show "?xs i"
        unfolding attack_order_def
        using i_less
        apply (simp only: nth_append length_replicate i_less if_True nth_replicate)
        done
    qed
    have tail_false: "\<And>i. i < ?m \<Longrightarrow> ?xs (?n+i) = False"
    proof -
      fix i
      assume i_less: "i < ?m"
      have index: "?n+i = length (replicate ?n True)+i"
        by simp
      have offset:
          "(replicate ?n True @ replicate ?m False) ! (?n+i) =
           replicate ?m False ! i"
        unfolding index by (rule nth_append_length_plus)
      show "?xs (?n+i) = False"
        unfolding attack_order_def
        using offset i_less
        apply (simp only: nth_replicate)
        done
    qed
    have tail_order: "\<And>i. i < ?m \<Longrightarrow> \<not> ?xs (?n+i)"
      using tail_false by simp
    have track_identity:
        "opt.Slack ?N = rz_power_track_slack a b beta1 eps k"
      unfolding rz_power_track_slack_def rz_power_u_bound_def
      by (simp add: algebra_simps)
    have raw_anchor_bound:
        "opt.A ?xs ?n \<le>
          ln (1 + real ?n * (exp opt.alpha - 1)) +
          real ?n * (opt.alpha * opt.Slack ?N)"
      by (rule opt.rz_anchor_log_bound[OF anchor_order])
        (use assumptions sample in auto)
    have anchor_bound:
        "opt.A ?xs ?n \<le> rz_power_anchor_bound a b c beta1 eps k"
      using raw_anchor_bound track_identity
      unfolding rz_power_anchor_bound_def by simp
    have burn_length: "rz_burn_index beta1 \<le> ?m-1"
      using assumptions by arith
    have burn_spec: "beta1^(rz_burn_index beta1) \<le>
        rz_tail_floor/(2*(1+rz_tail_floor))"
      by (rule rz_burn_index_spec[OF beta10 beta11])
    have floor_factor_positive: "0 < 1+rz_tail_floor"
      using rz_tail_floor_positive by linarith
    have burn_scaled:
        "(1+rz_tail_floor)*beta1^(rz_burn_index beta1) \<le>
         (1+rz_tail_floor)*(rz_tail_floor/(2*(1+rz_tail_floor)))"
      by (rule mult_left_mono[OF burn_spec])
        (use floor_factor_positive in linarith)
    have cancel_floor:
        "(1+rz_tail_floor)*(rz_tail_floor/(2*(1+rz_tail_floor))) =
         rz_tail_floor/2"
      using floor_factor_positive by (simp add: field_simps)
    have floor_momentum:
        "(1+rz_tail_floor)*beta1^(rz_burn_index beta1) \<le>
         rz_tail_floor/2"
      using burn_scaled cancel_floor by linarith
    have burn_momentum:
        "(1+sigmoid (-1))*beta1^(rz_burn_index beta1) \<le>
         sigmoid (-1)/2"
      using floor_momentum unfolding rz_tail_floor_def .
    have takeover_floor:
        "rz_power_anchor_bound a b c beta1 eps k +
          real (rz_burn_index beta1)*(2*?eta/eps) -
          real (?m-1-rz_burn_index beta1) *
            (?eta*rz_tail_floor/(2*(1+eps))) < 0"
      using assumptions by blast
    have takeover_factor:
        "?eta*rz_tail_floor/(2*(1+eps)) =
         ?eta*(sigmoid (-1)/2)/(1+eps)"
      using eps unfolding rz_tail_floor_def
      by (simp add: field_simps)
    have takeover:
        "rz_power_anchor_bound a b c beta1 eps k +
          real (rz_burn_index beta1)*(2*?eta/eps) -
          real ((?m-1)-rz_burn_index beta1) *
            (?eta*(sigmoid (-1)/2)/(1+eps)) < 0"
      using takeover_floor unfolding takeover_factor .
    have auxiliary_identity:
        "opt.UB ?N = rz_power_u_bound a b eps k"
      unfolding rz_power_u_bound_def
      by (simp add: algebra_simps)
    have total_count: "?n+?m \<le> ?N" using counts by simp
    have auxiliary_small: "opt.UB ?N \<le> 1"
      using assumptions auxiliary_identity by linarith
    have decay_half: "?eta*decay \<le> 1/2"
      using assumptions by blast
    have terminal_small:
        "?eta*rz_terminal_rate beta1 eps \<le> 1/2"
      using assumptions by blast
    have rate_small:
        "?eta*((1-beta1)*sigmoid (-2)/(1+eps)) \<le> 1/2"
      using terminal_small unfolding rz_terminal_rate_def .
    have auxiliary_dominated:
        "rz_power_u_bound a b eps k <
         ?eta*rz_terminal_rate beta1 eps"
      using assumptions by blast
    have auxiliary_dominated_expanded:
        "opt.UB ?N < ?eta*((1-beta1)*sigmoid (-2)/(1+eps))"
      using auxiliary_dominated auxiliary_identity
      unfolding rz_terminal_rate_def by linarith
    have strict: "opt.A ?xs (?n+?m) < - opt.Uc ?xs (?n+?m)"
      by (rule opt.rz_anchor_tail_strict_dominance
          [OF anchor_order tail_order total_count tail_positive anchor_bound
            burn_length burn_momentum takeover auxiliary_small decay_half
            rate_small auxiliary_dominated_expanded])
    show "rz_power_attack_main a b c beta1 beta2 eps decay k <
      - rz_power_attack_aux a b c beta1 beta2 eps decay k"
      using strict counts
      unfolding rz_power_attack_main_def rz_power_attack_aux_def by simp
  qed
qed


theorem rz_power_attack_aux_positive_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    0 < rz_power_attack_aux a b c beta1 beta2 eps decay k"
proof -
  have side: "\<forall>\<^sub>F k in sequentially.
      power_learning_rate b k*decay \<le> 1/2 \<and>
      power_learning_rate b k/eps \<le> 1 \<and>
      rz_power_u_bound a b eps k \<le> 1 \<and>
      rz_burn_index beta1+3 \<le> power_tail c k"
    by (rule rz_power_finite_side_conditions
        [OF noise rate tail beta10 beta11 eps decay])
  show ?thesis
  proof (rule eventually_mono[OF side])
    fix k
    assume conditions:
      "power_learning_rate b k*decay \<le> 1/2 \<and>
       power_learning_rate b k/eps \<le> 1 \<and>
       rz_power_u_bound a b eps k \<le> 1 \<and>
       rz_burn_index beta1+3 \<le> power_tail c k"
    let ?eta = "power_learning_rate b k"
    let ?kappa = "rz_power_kappa a k"
    let ?n = "power_anchor a c k"
    let ?m = "power_tail c k"
    let ?N = "power_population a k"
    let ?xs = "\<lambda>i. attack_order ?n ?m ! i"
    have eta_positive: "0 < ?eta" by (rule power_learning_rate_positive)
    have kappa_positive: "0 < ?kappa" by (rule rz_power_kappa_positive)
    have decay_step: "?eta*decay \<le> 1" using conditions by linarith
    interpret opt: rz_parameters ?eta beta1 beta2 eps decay ?kappa
      by unfold_locales
        (use eta_positive beta10 beta11 beta20 beta21 eps decay decay_step
          kappa_positive in auto)
    have positive: "0 < opt.Uc ?xs ?N"
      by (rule opt.rz_u_positive_gt[OF power_population_positive])
    show "0 < rz_power_attack_aux a b c beta1 beta2 eps decay k"
      using positive unfolding rz_power_attack_aux_def by simp
  qed
qed

theorem rz_power_attack_metrics_eventually:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "\<forall>\<^sub>F k in sequentially.
    realizable_test_risk (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
        1-power_tail_ratio a c k \<and>
    realizable_test_auc (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
        2*power_tail_ratio a c k-(power_tail_ratio a c k)^2"
proof -
  have dominance: "\<forall>\<^sub>F k in sequentially.
      rz_power_attack_main a b c beta1 beta2 eps decay k <
        - rz_power_attack_aux a b c beta1 beta2 eps decay k"
    by (rule rz_power_attack_dominance_eventually
        [OF noise rate tail beta10 beta11 beta20 beta21 eps decay])
  have auxiliary_positive: "\<forall>\<^sub>F k in sequentially.
      0 < rz_power_attack_aux a b c beta1 beta2 eps decay k"
    by (rule rz_power_attack_aux_positive_eventually
        [OF noise rate tail beta10 beta11 beta20 beta21 eps decay])
  show ?thesis
  proof (rule eventually_mono[OF eventually_conj[OF dominance auxiliary_positive]])
    fix k
    assume conditions:
      "rz_power_attack_main a b c beta1 beta2 eps decay k <
         - rz_power_attack_aux a b c beta1 beta2 eps decay k \<and>
       0 < rz_power_attack_aux a b c beta1 beta2 eps decay k"
    show "realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
          1-power_tail_ratio a c k \<and>
      realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
          2*power_tail_ratio a c k-(power_tail_ratio a c k)^2"
    proof
      show "realizable_test_risk (power_tail_ratio a c k)
          (rz_power_attack_main a b c beta1 beta2 eps decay k)
          (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
            1-power_tail_ratio a c k"
        by (rule realizable_test_risk_negative) (use conditions in auto)
      show "realizable_test_auc (power_tail_ratio a c k)
          (rz_power_attack_main a b c beta1 beta2 eps decay k)
          (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
            2*power_tail_ratio a c k-(power_tail_ratio a c k)^2"
        by (rule realizable_test_auc_attack) (use conditions in auto)
    qed
  qed
qed

theorem rz_power_attack_metric_limits:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "((\<lambda>k.
    (realizable_test_risk (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k),
     realizable_test_auc (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k)))
      \<longlongrightarrow> (1,0)) sequentially"
proof -
  have tail_limit:
      "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    by (rule power_tail_ratio_tendsto_zero[OF tail])
  have identities: "\<forall>\<^sub>F k in sequentially.
    realizable_test_risk (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
        1-power_tail_ratio a c k \<and>
    realizable_test_auc (power_tail_ratio a c k)
      (rz_power_attack_main a b c beta1 beta2 eps decay k)
      (rz_power_attack_aux a b c beta1 beta2 eps decay k) =
        2*power_tail_ratio a c k-(power_tail_ratio a c k)^2"
    by (rule rz_power_attack_metrics_eventually
        [OF noise rate tail beta10 beta11 beta20 beta21 eps decay])
  have risk_reference:
      "((\<lambda>k. 1-power_tail_ratio a c k) \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const tail_limit] by simp
  have auc_reference: "((\<lambda>k.
      2*power_tail_ratio a c k-(power_tail_ratio a c k)^2)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_diff[OF tendsto_mult[OF tendsto_const tail_limit]
      tendsto_power[OF tail_limit, of 2]] by simp
  have risk_identity: "\<forall>\<^sub>F k in sequentially.
      1-power_tail_ratio a c k =
      realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k)"
    using identities by eventually_elim simp
  have auc_identity: "\<forall>\<^sub>F k in sequentially.
      2*power_tail_ratio a c k-(power_tail_ratio a c k)^2 =
      realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k)"
    using identities by eventually_elim simp
  have risk_limit: "((\<lambda>k.
      realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k))
      \<longlongrightarrow> 1) sequentially"
    by (rule Lim_transform_eventually[OF risk_reference risk_identity])
  have auc_limit: "((\<lambda>k.
      realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k))
      \<longlongrightarrow> 0) sequentially"
    by (rule Lim_transform_eventually[OF auc_reference auc_identity])
  show ?thesis by (intro tendsto_Pair risk_limit auc_limit)
qed


theorem rz_power_law_adamw_inversion:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps" and decay: "0 \<le> decay"
  shows "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    and "(power_confidence \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. rz_power_random_benign_probability
      a b c beta1 beta2 eps decay k) \<longlongrightarrow> 1) sequentially"
    and "((\<lambda>k.
      (realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k),
       realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k)))
      \<longlongrightarrow> (1,0)) sequentially"
proof -
  show "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    by (rule power_tail_ratio_tendsto_zero[OF tail])
  show "(power_confidence \<longlongrightarrow> 0) sequentially"
    by (rule power_confidence_tendsto_zero)
  show "((\<lambda>k. rz_power_random_benign_probability
      a b c beta1 beta2 eps decay k) \<longlongrightarrow> 1) sequentially"
    by (rule rz_power_random_probability_tendsto_one
        [OF noise rate tail beta10 beta11 beta20 beta21 eps decay])
  show "((\<lambda>k.
      (realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k),
       realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps decay k)
        (rz_power_attack_aux a b c beta1 beta2 eps decay k)))
      \<longlongrightarrow> (1,0)) sequentially"
    by (rule rz_power_attack_metric_limits
        [OF noise rate tail beta10 beta11 beta20 beta21 eps decay])
qed

corollary rz_power_law_adam_inversion:
  assumes noise: "a < 2*b" and rate: "b < c" and tail: "c < a"
    and beta10: "0 \<le> beta1" and beta11: "beta1 < 1"
    and beta20: "0 \<le> beta2" and beta21: "beta2 < 1"
    and eps: "0 < eps"
  shows "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    and "(power_confidence \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. rz_power_random_benign_probability
      a b c beta1 beta2 eps 0 k) \<longlongrightarrow> 1) sequentially"
    and "((\<lambda>k.
      (realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps 0 k)
        (rz_power_attack_aux a b c beta1 beta2 eps 0 k),
       realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps 0 k)
        (rz_power_attack_aux a b c beta1 beta2 eps 0 k)))
      \<longlongrightarrow> (1,0)) sequentially"
proof -
  show "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    by (rule power_tail_ratio_tendsto_zero[OF tail])
  show "(power_confidence \<longlongrightarrow> 0) sequentially"
    by (rule power_confidence_tendsto_zero)
  have decay0: "(0::real) \<le> 0" by simp
  show "((\<lambda>k. rz_power_random_benign_probability
      a b c beta1 beta2 eps 0 k) \<longlongrightarrow> 1) sequentially"
    by (rule rz_power_random_probability_tendsto_one
        [where decay=0,
         OF noise rate tail beta10 beta11 beta20 beta21 eps decay0])
  show "((\<lambda>k.
      (realizable_test_risk (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps 0 k)
        (rz_power_attack_aux a b c beta1 beta2 eps 0 k),
       realizable_test_auc (power_tail_ratio a c k)
        (rz_power_attack_main a b c beta1 beta2 eps 0 k)
        (rz_power_attack_aux a b c beta1 beta2 eps 0 k)))
      \<longlongrightarrow> (1,0)) sequentially"
    by (rule rz_power_attack_metric_limits
        [where decay=0,
         OF noise rate tail beta10 beta11 beta20 beta21 eps decay0])
qed

end