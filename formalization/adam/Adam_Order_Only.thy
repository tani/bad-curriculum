theory Adam_Order_Only
  imports Adam_Bridge
begin

section \<open>Adam specialization\<close>

definition adam_state ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> aw_state" where
  "adam_state eta beta1 beta2 eps b k =
    aw_run eta beta1 beta2 eps 0 b k"

definition adam_weight ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adam_weight eta beta1 beta2 eps b k =
    aw_weight (adam_state eta beta1 beta2 eps b k)"

definition adam_first_moment ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adam_first_moment eta beta1 beta2 eps b k =
    aw_first (adam_state eta beta1 beta2 eps b k)"

definition adam_second_moment ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adam_second_moment eta beta1 beta2 eps b k =
    aw_second (adam_state eta beta1 beta2 eps b k)"

locale adam_parameters =
  fixes eta beta1 beta2 eps :: real
  assumes eta_pos: "0 < eta"
    and beta1_nonneg: "0 \<le> beta1" and beta1_lt: "beta1 < 1"
    and beta2_nonneg: "0 \<le> beta2" and beta2_lt: "beta2 < 1"
    and eps_pos: "0 < eps"
begin

sublocale core: aw_parameters eta beta1 beta2 eps 0
  by standard (use eta_pos beta1_nonneg beta1_lt beta2_nonneg beta2_lt eps_pos in auto)

lemma adam_initial [simp]:
  "adam_weight eta beta1 beta2 eps b 0 = 0"
  "adam_first_moment eta beta1 beta2 eps b 0 = 0"
  "adam_second_moment eta beta1 beta2 eps b 0 = 0"
  by (simp_all add: adam_weight_def adam_first_moment_def
      adam_second_moment_def adam_state_def aw_zero_def)

lemma adam_state_recurrence:
  "adam_state eta beta1 beta2 eps b (Suc k) =
    aw_step eta beta1 beta2 eps 0 (Suc k) (b k)
      (adam_state eta beta1 beta2 eps b k)"
  by (simp add: adam_state_def)

theorem adam_anchor_tail_inversion:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and anchor_bound: "adam_weight eta beta1 beta2 eps b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "h + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "adam_weight eta beta1 beta2 eps b (n+m) < 0"
proof -
  have core_bound: "aw_weight (aw_run eta beta1 beta2 eps 0 b n) \<le> h"
    using anchor_bound by (simp add: adam_weight_def adam_state_def)
  have negative: "aw_weight (aw_run eta beta1 beta2 eps 0 b (n+m)) < 0"
    by (rule core.aw_anchor_tail_inversion[OF anchor tail core_bound
          burn_length burn_momentum takeover])
  show ?thesis using negative by (simp add: adam_weight_def adam_state_def)
qed

corollary adam_attack_metrics:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and anchor_bound: "adam_weight eta beta1 beta2 eps b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "h + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p (adam_weight eta beta1 beta2 eps b (n+m)) = 1-p"
    and "clean_test_auc p (adam_weight eta beta1 beta2 eps b (n+m)) = p"
proof -
  have negative: "adam_weight eta beta1 beta2 eps b (n+m) < 0"
    by (rule adam_anchor_tail_inversion[OF anchor tail anchor_bound
          burn_length burn_momentum takeover])
  show "clean_test_risk p (adam_weight eta beta1 beta2 eps b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p (adam_weight eta beta1 beta2 eps b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

text \<open>
  The anchor bound is no longer a premise below: it is the explicit
  logarithmic value supplied by the bridge theory.
\<close>

theorem adam_anchor_tail_inversion_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "eta/eps \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "core.Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "adam_weight eta beta1 beta2 eps b (n+m) < 0"
proof -
  have negative: "aw_weight (aw_run eta beta1 beta2 eps 0 b (n+m)) < 0"
    by (rule core.aw_anchor_tail_inversion_explicit[where b=b and n=n and m=m
          and J=J, OF anchor tail alpha_le burn_length burn_momentum takeover])
  show ?thesis using negative by (simp add: adam_weight_def adam_state_def)
qed

corollary adam_attack_metrics_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "eta/eps \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "core.Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p (adam_weight eta beta1 beta2 eps b (n+m)) = 1-p"
    and "clean_test_auc p (adam_weight eta beta1 beta2 eps b (n+m)) = p"
proof -
  have negative: "adam_weight eta beta1 beta2 eps b (n+m) < 0"
    by (rule adam_anchor_tail_inversion_explicit[where b=b and n=n and m=m
          and J=J, OF anchor tail alpha_le burn_length burn_momentum takeover])
  show "clean_test_risk p (adam_weight eta beta1 beta2 eps b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p (adam_weight eta beta1 beta2 eps b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

theorem adam_random_order_benign_probability:
  fixes conf delta :: real
  assumes N_positive: "0 < N" and sample_size: "n \<le> N"
    and conf_positive: "0 < conf" and conf_at_most_one: "conf \<le> 1"
    and drift_nonneg: "0 \<le> core.Adrift delta (real n / real N)"
    and landing: "0 < delta - 2*eta/eps -
      core.Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
    and total: "0 < core.Adrift delta (real n / real N) * real N -
      core.Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
  shows "1 - conf \<le> uniform_probability (binary_orders n N)
    {xs. 0 < adam_weight eta beta1 beta2 eps (\<lambda>i. xs ! i) N}"
proof -
  have core_bound: "1 - conf \<le> uniform_probability (binary_orders n N)
      {xs. 0 < aw_weight (aw_run eta beta1 beta2 eps 0 (\<lambda>i. xs ! i) N)}"
    by (rule core.aw_random_order_benign_probability[OF N_positive sample_size
          conf_positive conf_at_most_one drift_nonneg landing total])
  show ?thesis
    using core_bound by (simp add: adam_weight_def adam_state_def)
qed

end

end
