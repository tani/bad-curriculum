theory AdamW_Order_Only
  imports "../adam/Adam_Bridge"
begin

section \<open>AdamW specialization with decoupled weight decay\<close>

definition adamw_state ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> aw_state" where
  "adamw_state eta beta1 beta2 eps decay b k =
    aw_run eta beta1 beta2 eps decay b k"

definition adamw_weight ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adamw_weight eta beta1 beta2 eps decay b k =
    aw_weight (adamw_state eta beta1 beta2 eps decay b k)"

definition adamw_first_moment ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adamw_first_moment eta beta1 beta2 eps decay b k =
    aw_first (adamw_state eta beta1 beta2 eps decay b k)"

definition adamw_second_moment ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "adamw_second_moment eta beta1 beta2 eps decay b k =
    aw_second (adamw_state eta beta1 beta2 eps decay b k)"

locale adamw_parameters =
  fixes eta beta1 beta2 eps decay :: real
  assumes eta_pos: "0 < eta"
    and beta1_nonneg: "0 \<le> beta1" and beta1_lt: "beta1 < 1"
    and beta2_nonneg: "0 \<le> beta2" and beta2_lt: "beta2 < 1"
    and eps_pos: "0 < eps"
    and decay_nonneg: "0 \<le> decay"
    and decay_step: "eta * decay \<le> 1"
begin

sublocale core: aw_parameters eta beta1 beta2 eps decay
  by standard (use eta_pos beta1_nonneg beta1_lt beta2_nonneg beta2_lt
      eps_pos decay_nonneg decay_step in auto)

lemma adamw_initial [simp]:
  "adamw_weight eta beta1 beta2 eps decay b 0 = 0"
  "adamw_first_moment eta beta1 beta2 eps decay b 0 = 0"
  "adamw_second_moment eta beta1 beta2 eps decay b 0 = 0"
  by (simp_all add: adamw_weight_def adamw_first_moment_def
      adamw_second_moment_def adamw_state_def aw_zero_def)

lemma adamw_state_recurrence:
  "adamw_state eta beta1 beta2 eps decay b (Suc k) =
    aw_step eta beta1 beta2 eps decay (Suc k) (b k)
      (adamw_state eta beta1 beta2 eps decay b k)"
  by (simp add: adamw_state_def)

theorem adamw_anchor_tail_inversion:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and anchor_bound: "adamw_weight eta beta1 beta2 eps decay b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "h + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "adamw_weight eta beta1 beta2 eps decay b (n+m) < 0"
proof -
  have core_bound:
      "aw_weight (aw_run eta beta1 beta2 eps decay b n) \<le> h"
    using anchor_bound by (simp add: adamw_weight_def adamw_state_def)
  have negative:
      "aw_weight (aw_run eta beta1 beta2 eps decay b (n+m)) < 0"
    by (rule core.aw_anchor_tail_inversion[OF anchor tail core_bound
          burn_length burn_momentum takeover])
  show ?thesis using negative by (simp add: adamw_weight_def adamw_state_def)
qed

corollary adamw_attack_metrics:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and anchor_bound: "adamw_weight eta beta1 beta2 eps decay b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "h + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = 1-p"
    and "clean_test_auc p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = p"
proof -
  have negative: "adamw_weight eta beta1 beta2 eps decay b (n+m) < 0"
    by (rule adamw_anchor_tail_inversion[OF anchor tail anchor_bound
          burn_length burn_momentum takeover])
  show "clean_test_risk p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

text \<open>
  The anchor bound is no longer a premise below: it is the explicit
  logarithmic value supplied by the bridge theory, and it holds for every
  admissible decoupled weight decay.
\<close>

theorem adamw_anchor_tail_inversion_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "eta/eps \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "core.Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "adamw_weight eta beta1 beta2 eps decay b (n+m) < 0"
proof -
  have negative: "aw_weight (aw_run eta beta1 beta2 eps decay b (n+m)) < 0"
    by (rule core.aw_anchor_tail_inversion_explicit[where b=b and n=n and m=m
          and J=J, OF anchor tail alpha_le burn_length burn_momentum takeover])
  show ?thesis using negative by (simp add: adamw_weight_def adamw_state_def)
qed

corollary adamw_attack_metrics_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "eta/eps \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "core.Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = 1-p"
    and "clean_test_auc p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = p"
proof -
  have negative: "adamw_weight eta beta1 beta2 eps decay b (n+m) < 0"
    by (rule adamw_anchor_tail_inversion_explicit[where b=b and n=n and m=m
          and J=J, OF anchor tail alpha_le burn_length burn_momentum takeover])
  show "clean_test_risk p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p
      (adamw_weight eta beta1 beta2 eps decay b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

theorem adamw_random_order_benign_probability:
  fixes conf delta :: real
  assumes N_positive: "0 < N" and sample_size: "n \<le> N"
    and conf_positive: "0 < conf" and conf_at_most_one: "conf \<le> 1"
    and drift_nonneg: "0 \<le> core.Adrift delta (real n / real N)"
    and landing: "0 < delta - 2*eta/eps -
      core.Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
    and total: "0 < core.Adrift delta (real n / real N) * real N -
      core.Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
  shows "1 - conf \<le> uniform_probability (binary_orders n N)
    {xs. 0 < adamw_weight eta beta1 beta2 eps decay (\<lambda>i. xs ! i) N}"
proof -
  have core_bound: "1 - conf \<le> uniform_probability (binary_orders n N)
      {xs. 0 < aw_weight (aw_run eta beta1 beta2 eps decay (\<lambda>i. xs ! i) N)}"
    by (rule core.aw_random_order_benign_probability[OF N_positive sample_size
          conf_positive conf_at_most_one drift_nonneg landing total])
  show ?thesis
    using core_bound by (simp add: adamw_weight_def adamw_state_def)
qed

end

end
