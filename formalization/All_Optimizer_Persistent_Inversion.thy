theory All_Optimizer_Persistent_Inversion
  imports
    "core/Persistent_Epoch_Inversion"
    "sgd/SGD_Order_Only"
    "momentum-sgd/Momentum_SGD_Order_Only"
    "adam/Adam_Order_Only"
    "adamw/AdamW_Order_Only"
begin

section \<open>The two repeated orders\<close>

definition anchor_tail_stream :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "anchor_tail_stream n m k \<longleftrightarrow> k mod (n+m) < n"

definition tail_anchor_stream :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "tail_anchor_stream n m k \<longleftrightarrow> m \<le> k mod (n+m)"

lemma anchor_tail_stream_anchor:
  assumes "i < n"
  shows "anchor_tail_stream n m (e*(n+m)+i)"
  using assms by (simp add: anchor_tail_stream_def)

lemma anchor_tail_stream_tail:
  assumes "i < m"
  shows "\<not> anchor_tail_stream n m (e*(n+m)+n+i)"
proof -
  have positive: "0 < n+m" using assms by linarith
  have less: "n+i < n+m" using assms by linarith
  show ?thesis using positive less
    by (simp add: anchor_tail_stream_def add.assoc)
qed

lemma tail_anchor_stream_tail:
  assumes "i < m"
  shows "\<not> tail_anchor_stream n m (e*(n+m)+i)"
  using assms by (simp add: tail_anchor_stream_def)

lemma tail_anchor_stream_anchor:
  assumes "i < n"
  shows "tail_anchor_stream n m (e*(n+m)+m+i)"
proof -
  have positive: "0 < n+m" using assms by linarith
  have less: "m+i < n+m" using assms by linarith
  show ?thesis using positive less
    by (simp add: tail_anchor_stream_def add.assoc)
qed

section \<open>Plain SGD and Momentum SGD with an infinite presentation stream\<close>

primrec persistent_sgd_weight :: "real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "persistent_sgd_weight eta b 0 = 0"
| "persistent_sgd_weight eta b (Suc k) = persistent_sgd_weight eta b k -
    eta * (sigmoid (persistent_sgd_weight eta b k) - bool_value (b k))"

primrec persistent_sgd_moment :: "real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "persistent_sgd_moment eta b 0 = 0"
| "persistent_sgd_moment eta b (Suc k) =
    sigmoid (persistent_sgd_weight eta b k) - bool_value (b k)"

primrec persistent_momentum_state ::
    "real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "persistent_momentum_state eta mu b 0 = (0,0)"
| "persistent_momentum_state eta mu b (Suc k) =
    (let z = persistent_momentum_state eta mu b k;
         g = sigmoid (fst z) - bool_value (b k);
         v = mu * snd z + g
     in (fst z - eta*v, v))"

definition persistent_momentum_weight ::
    "real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "persistent_momentum_weight eta mu b k =
    fst (persistent_momentum_state eta mu b k)"

definition persistent_momentum_moment ::
    "real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "persistent_momentum_moment eta mu b k =
    (1-mu) * snd (persistent_momentum_state eta mu b k)"

lemma persistent_momentum_initial [simp]:
  "persistent_momentum_weight eta mu b 0 = 0"
  "persistent_momentum_moment eta mu b 0 = 0"
  by (simp_all add: persistent_momentum_weight_def persistent_momentum_moment_def)

lemma persistent_momentum_step:
  "persistent_momentum_weight eta mu b (Suc k) =
      persistent_momentum_weight eta mu b k -
        eta * (mu * snd (persistent_momentum_state eta mu b k) +
          sigmoid (persistent_momentum_weight eta mu b k) - bool_value (b k))"
  "persistent_momentum_moment eta mu b (Suc k) =
      mu * persistent_momentum_moment eta mu b k +
        (1-mu) * (sigmoid (persistent_momentum_weight eta mu b k) -
          bool_value (b k))"
  by (simp_all add: persistent_momentum_weight_def persistent_momentum_moment_def
        Let_def algebra_simps)

lemma sgd_persistent_update:
  assumes eta_positive: "0 < eta"
  shows "persistent_update 0 1 eta eta (\<lambda>_. eta) b
    (persistent_sgd_weight eta b) (persistent_sgd_moment eta b)"
proof (unfold_locales)
  show "(0::real) \<le> 0" by simp
  show "(0::real) < 1" by simp
  show "(0::real) \<le> 1" by simp
  show "(1::real) \<le> 1" by simp
  show "0 < eta" by (rule eta_positive)
  show "\<And>k. eta \<le> (\<lambda>_. eta) (Suc k)" by simp
  
  show "persistent_sgd_weight eta b 0 = 0" by simp
  show "persistent_sgd_moment eta b 0 = 0" by simp
  show "\<And>k. persistent_sgd_moment eta b (Suc k) =
      0 * persistent_sgd_moment eta b k +
      (1-0) * (sigmoid (persistent_sgd_weight eta b k) - bool_value (b k))"
    by simp
  show "\<And>k. persistent_sgd_weight eta b (Suc k) =
      1 * persistent_sgd_weight eta b k -
      (\<lambda>_. eta) (Suc k) * persistent_sgd_moment eta b (Suc k)"
    by simp
qed

theorem sgd_persistent_epoch_inversion:
  assumes eta_positive: "0 < eta"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "(0::real)^J \<le> 1/6"
    and anchor_long: "real m*eta + real J*eta <
      real ((n-1)-J) * (eta/4)"
    and tail_long: "real n*eta + real J*eta <
      real ((m-1)-J) * (eta/4)"
    and epoch: "1 \<le> E"
  shows "persistent_sgd_weight eta (anchor_tail_stream n m) (E*(n+m)) < 0 \<and>
    0 < persistent_sgd_weight eta (tail_anchor_stream n m) (E*(n+m))"
proof -
  interpret attack: persistent_update 0 1 eta eta "\<lambda>_. eta"
    "anchor_tail_stream n m"
    "persistent_sgd_weight eta (anchor_tail_stream n m)"
    "persistent_sgd_moment eta (anchor_tail_stream n m)"
    by (rule sgd_persistent_update[OF eta_positive])
  interpret reverse: persistent_update 0 1 eta eta "\<lambda>_. eta"
    "tail_anchor_stream n m"
    "persistent_sgd_weight eta (tail_anchor_stream n m)"
    "persistent_sgd_moment eta (tail_anchor_stream n m)"
    by (rule sgd_persistent_update[OF eta_positive])
  have negative: "persistent_sgd_weight eta (anchor_tail_stream n m)
      (E*(n+m)) < 0"
    using attack.anchor_tail_all_epochs_negative[OF anchor_tail_stream_anchor
          anchor_tail_stream_tail sizes burn anchor_long tail_long epoch] by blast
  have positive: "0 < persistent_sgd_weight eta (tail_anchor_stream n m)
      (E*(n+m))"
    using reverse.tail_anchor_all_epochs_positive[OF tail_anchor_stream_tail
          tail_anchor_stream_anchor sizes burn anchor_long tail_long epoch] by blast
  show ?thesis using negative positive by blast
qed

corollary sgd_persistent_epoch_metrics:
  assumes inversion: "persistent_sgd_weight eta (anchor_tail_stream n m)
      (E*(n+m)) < 0 \<and>
    0 < persistent_sgd_weight eta (tail_anchor_stream n m) (E*(n+m))"
  shows "clean_test_risk p (persistent_sgd_weight eta (anchor_tail_stream n m)
        (E*(n+m))) = 1-p \<and>
    clean_test_auc p (persistent_sgd_weight eta (anchor_tail_stream n m)
        (E*(n+m))) = p \<and>
    clean_test_risk p (persistent_sgd_weight eta (tail_anchor_stream n m)
        (E*(n+m))) = p \<and>
    clean_test_auc p (persistent_sgd_weight eta (tail_anchor_stream n m)
        (E*(n+m))) = 1-p"
proof -
  have negative: "persistent_sgd_weight eta (anchor_tail_stream n m)
      (E*(n+m)) < 0" using inversion by blast
  have positive: "0 < persistent_sgd_weight eta (tail_anchor_stream n m)
      (E*(n+m))" using inversion by blast
  show ?thesis using clean_test_risk_negative[OF negative]
    clean_test_auc_negative[OF negative]
    clean_test_risk_positive[OF positive]
    clean_test_auc_positive[OF positive] by blast
qed
section \<open>Momentum SGD\<close>

lemma persistent_momentum_weight_rec:
  assumes "mu < 1"
  shows "persistent_momentum_weight eta mu b (Suc k) =
    persistent_momentum_weight eta mu b k -
      (eta/(1-mu)) * persistent_momentum_moment eta mu b (Suc k)"
proof -
  let ?v = "mu * snd (persistent_momentum_state eta mu b k) +
    sigmoid (persistent_momentum_weight eta mu b k) - bool_value (b k)"
  have nonzero: "1-mu \<noteq> 0" using assms by linarith
  have weight_step: "persistent_momentum_weight eta mu b (Suc k) =
      persistent_momentum_weight eta mu b k - eta * ?v"
    by (rule persistent_momentum_step(1))
  have moment_step: "persistent_momentum_moment eta mu b (Suc k) =
      (1-mu) * ?v"
    by (simp add: persistent_momentum_moment_def persistent_momentum_weight_def
          Let_def algebra_simps)
  have scaled: "(eta/(1-mu)) * persistent_momentum_moment eta mu b (Suc k) =
      eta * ?v"
    unfolding moment_step using nonzero by simp
  show ?thesis using weight_step scaled by simp
qed
lemma momentum_persistent_update:
  assumes eta_positive: "0 < eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
  shows "persistent_update mu 1 (eta/(1-mu)) (eta/(1-mu))
    (\<lambda>_. eta/(1-mu)) b
    (persistent_momentum_weight eta mu b)
    (persistent_momentum_moment eta mu b)"
proof (unfold_locales)
  show "0 \<le> mu" by (rule mu_nonnegative)
  show "mu < 1" by (rule mu_less_one)
  show "(0::real) \<le> 1" by simp
  show "(1::real) \<le> 1" by simp
  show "0 < eta/(1-mu)"
    by (rule divide_pos_pos) (use eta_positive mu_less_one in linarith)+
  show "\<And>k. eta/(1-mu) \<le> (\<lambda>_. eta/(1-mu)) (Suc k)" by simp
  show "persistent_momentum_weight eta mu b 0 = 0" by simp
  show "persistent_momentum_moment eta mu b 0 = 0" by simp
  show "\<And>k. persistent_momentum_moment eta mu b (Suc k) =
      mu * persistent_momentum_moment eta mu b k +
      (1-mu) * (sigmoid (persistent_momentum_weight eta mu b k) -
        bool_value (b k))"
    by (rule persistent_momentum_step(2))
  show "\<And>k. persistent_momentum_weight eta mu b (Suc k) =
      1 * persistent_momentum_weight eta mu b k -
      (\<lambda>_. eta/(1-mu)) (Suc k) *
        persistent_momentum_moment eta mu b (Suc k)"
    using persistent_momentum_weight_rec[OF mu_less_one] by simp
qed

theorem momentum_persistent_epoch_inversion:
  assumes eta_positive: "0 < eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "mu^J \<le> 1/6"
    and anchor_long: "real m*c + real J*c <
      real ((n-1)-J) * (c/4)"
    and tail_long: "real n*c + real J*c <
      real ((m-1)-J) * (c/4)"
    and c_def: "c = eta/(1-mu)"
    and epoch: "1 \<le> E"
  shows "persistent_momentum_weight eta mu (anchor_tail_stream n m)
      (E*(n+m)) < 0 \<and>
    0 < persistent_momentum_weight eta mu (tail_anchor_stream n m)
      (E*(n+m))"
proof -
  interpret attack: persistent_update mu 1 c c "\<lambda>_. c"
    "anchor_tail_stream n m"
    "persistent_momentum_weight eta mu (anchor_tail_stream n m)"
    "persistent_momentum_moment eta mu (anchor_tail_stream n m)"
    unfolding c_def by (rule momentum_persistent_update[OF eta_positive
          mu_nonnegative mu_less_one])
  interpret reverse: persistent_update mu 1 c c "\<lambda>_. c"
    "tail_anchor_stream n m"
    "persistent_momentum_weight eta mu (tail_anchor_stream n m)"
    "persistent_momentum_moment eta mu (tail_anchor_stream n m)"
    unfolding c_def by (rule momentum_persistent_update[OF eta_positive
          mu_nonnegative mu_less_one])
  have negative: "persistent_momentum_weight eta mu (anchor_tail_stream n m)
      (E*(n+m)) < 0"
    using attack.anchor_tail_all_epochs_negative[OF anchor_tail_stream_anchor
          anchor_tail_stream_tail sizes burn anchor_long tail_long epoch] by blast
  have positive: "0 < persistent_momentum_weight eta mu
      (tail_anchor_stream n m) (E*(n+m))"
    using reverse.tail_anchor_all_epochs_positive[OF tail_anchor_stream_tail
          tail_anchor_stream_anchor sizes burn anchor_long tail_long epoch] by blast
  show ?thesis using negative positive by blast
qed

corollary momentum_persistent_epoch_metrics:
  assumes inversion: "persistent_momentum_weight eta mu (anchor_tail_stream n m)
      (E*(n+m)) < 0 \<and>
    0 < persistent_momentum_weight eta mu (tail_anchor_stream n m)
      (E*(n+m))"
  shows "clean_test_risk p (persistent_momentum_weight eta mu
        (anchor_tail_stream n m) (E*(n+m))) = 1-p \<and>
    clean_test_auc p (persistent_momentum_weight eta mu
        (anchor_tail_stream n m) (E*(n+m))) = p \<and>
    clean_test_risk p (persistent_momentum_weight eta mu
        (tail_anchor_stream n m) (E*(n+m))) = p \<and>
    clean_test_auc p (persistent_momentum_weight eta mu
        (tail_anchor_stream n m) (E*(n+m))) = 1-p"
proof -
  have negative: "persistent_momentum_weight eta mu (anchor_tail_stream n m)
      (E*(n+m)) < 0" using inversion by blast
  have positive: "0 < persistent_momentum_weight eta mu (tail_anchor_stream n m)
      (E*(n+m))" using inversion by blast
  show ?thesis using clean_test_risk_negative[OF negative]
    clean_test_auc_negative[OF negative]
    clean_test_risk_positive[OF positive]
    clean_test_auc_positive[OF positive] by blast
qed

section \<open>Exact Adam and AdamW adapter\<close>

context aw_parameters
begin

definition aw_effective_step :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "aw_effective_step b t = eta / ((1-beta1^t) * D b t)"

lemma aw_bias_lower:
  "1-beta1 \<le> 1-beta1^(Suc k)"
proof -
  have "beta1^(Suc k) \<le> beta1^1"
    by (rule aw_power_antimono[OF beta1_nonneg])
      (use beta1_lt in auto)
  then show ?thesis by simp
qed

lemma aw_effective_step_positive:
  "0 < aw_effective_step b (Suc k)"
proof -
  have bias: "0 < 1-beta1^(Suc k)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by blast
  have denominator: "0 < D b (Suc k)" by (rule aw_den_positive)
  show ?thesis unfolding aw_effective_step_def
    by (rule divide_pos_pos[OF eta_pos mult_pos_pos[OF bias denominator]])
qed

lemma aw_effective_step_lower:
  "eta/(1+eps) \<le> aw_effective_step b (Suc k)"
proof -
  have bias: "0 < 1-beta1^(Suc k)"
    "1-beta1^(Suc k) \<le> 1"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by auto
  have denominator: "0 < D b (Suc k)" "D b (Suc k) \<le> 1+eps"
    using aw_den_positive aw_den_bounds(2) by auto
  have product: "(1-beta1^(Suc k)) * D b (Suc k) \<le> 1+eps"
    using mult_mono[OF bias(2) denominator(2)] bias(1) denominator(1) by simp
  show ?thesis unfolding aw_effective_step_def
  proof (rule divide_left_mono[OF product])
    show "0 \<le> eta" using eta_pos by linarith
    show "0 < (1+eps) * ((1-beta1^(Suc k)) * D b (Suc k))"
    proof (rule mult_pos_pos)
      show "0 < 1+eps" using eps_pos by linarith
      show "0 < (1-beta1^(Suc k)) * D b (Suc k)"
        by (rule mult_pos_pos[OF bias(1) denominator(1)])
    qed
  qed
qed

lemma aw_effective_step_upper:
  "aw_effective_step b (Suc k) \<le> eta/(eps*(1-beta1))"
proof -
  have beta_gap: "0 < 1-beta1" using beta1_lt by linarith
  have bias: "0 < 1-beta1^(Suc k)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by blast
  have denominator: "0 < D b (Suc k)" by (rule aw_den_positive)
have product_order: "(1-beta1)*eps \<le>
      (1-beta1^(Suc k)) * D b (Suc k)"
  proof (rule mult_mono)
    show "1-beta1 \<le> 1-beta1^(Suc k)" by (rule aw_bias_lower)
    show "eps \<le> D b (Suc k)" by (rule aw_den_bounds(1))
    show "0 \<le> 1-beta1^(Suc k)" using bias by linarith
    show "0 \<le> eps" using eps_pos by linarith
  qed
  have product: "eps*(1-beta1) \<le> (1-beta1^(Suc k)) * D b (Suc k)"
    using product_order by (simp add: mult.commute)
  show ?thesis unfolding aw_effective_step_def
  proof (rule divide_left_mono[OF product])
    show "0 \<le> eta" using eta_pos by linarith
    show "0 < ((1-beta1^(Suc k)) * D b (Suc k)) * (eps*(1-beta1))"
    proof (rule mult_pos_pos)
      show "0 < (1-beta1^(Suc k)) * D b (Suc k)"
        by (rule mult_pos_pos[OF bias denominator])
      show "0 < eps*(1-beta1)"
        by (rule mult_pos_pos[OF eps_pos beta_gap])
    qed  qed
qed

lemma aw_effective_weight_rec:
  "W b (Suc k) = (1-eta*decay) * W b k -
    aw_effective_step b (Suc k) * M b (Suc k)"
proof -
  have bias: "1-beta1^(Suc k) \<noteq> 0"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by auto
  have denominator: "D b (Suc k) \<noteq> 0"
    using aw_den_positive[of b k] by linarith
  have direction: "eta * MH b (Suc k) / D b (Suc k) =
      aw_effective_step b (Suc k) * M b (Suc k)"
    unfolding aw_effective_step_def using bias denominator
    by (simp add: field_simps)
  show ?thesis using aw_w_rec[of b k] direction by simp
qed

lemma aw_persistent_update:
  "persistent_update beta1 (1-eta*decay) (eta/(1+eps))
    (eta/(eps*(1-beta1))) (aw_effective_step b) b (W b) (M b)"
proof (unfold_locales)
  show "0 \<le> beta1" by (rule beta1_nonneg)
  show "beta1 < 1" by (rule beta1_lt)
  show "0 \<le> 1-eta*decay" using decay_step by linarith
  show "1-eta*decay \<le> 1"
  proof -
    have "0 \<le> eta*decay"
      by (rule mult_nonneg_nonneg) (use eta_pos decay_nonneg in auto)
    then show ?thesis by linarith
  qed
  show "0 < eta/(1+eps)"
    by (rule divide_pos_pos) (use eta_pos eps_pos in linarith)+
  show "\<And>k. eta/(1+eps) \<le> aw_effective_step b (Suc k)"
    by (rule aw_effective_step_lower)
  show "\<And>k. aw_effective_step b (Suc k) \<le> eta/(eps*(1-beta1))"
    by (rule aw_effective_step_upper)
  show "W b 0 = 0" by (rule aw_initial(1))
  show "M b 0 = 0" by (rule aw_initial(2))
  show "\<And>k. M b (Suc k) = beta1 * M b k +
      (1-beta1) * (sigmoid (W b k) - bool_value (b k))"
    by (rule aw_m_rec)
  show "\<And>k. W b (Suc k) = (1-eta*decay) * W b k -
      aw_effective_step b (Suc k) * M b (Suc k)"
    by (rule aw_effective_weight_rec)
qed

theorem adamw_persistent_epoch_inversion:
  assumes sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta1^J \<le> 1/6"
    and anchor_long: "real m*(eta/(eps*(1-beta1))) +
      real J*(eta/(eps*(1-beta1))) <
      real ((n-1)-J) * ((eta/(1+eps))/4)"
    and tail_long: "real n*(eta/(eps*(1-beta1))) +
      real J*(eta/(eps*(1-beta1))) <
      real ((m-1)-J) * ((eta/(1+eps))/4)"
    and epoch: "1 \<le> E"
  shows "aw_weight (aw_run eta beta1 beta2 eps decay
        (anchor_tail_stream n m) (E*(n+m))) < 0 \<and>
    0 < aw_weight (aw_run eta beta1 beta2 eps decay
        (tail_anchor_stream n m) (E*(n+m)))"
proof -
  interpret attack: persistent_update beta1 "1-eta*decay" "eta/(1+eps)"
    "eta/(eps*(1-beta1))" "aw_effective_step (anchor_tail_stream n m)"
    "anchor_tail_stream n m" "W (anchor_tail_stream n m)"
    "M (anchor_tail_stream n m)"
    by (rule aw_persistent_update)
  interpret reverse: persistent_update beta1 "1-eta*decay" "eta/(1+eps)"
    "eta/(eps*(1-beta1))" "aw_effective_step (tail_anchor_stream n m)"
    "tail_anchor_stream n m" "W (tail_anchor_stream n m)"
    "M (tail_anchor_stream n m)"
    by (rule aw_persistent_update)
  have negative: "W (anchor_tail_stream n m) (E*(n+m)) < 0"
    using attack.anchor_tail_all_epochs_negative[OF anchor_tail_stream_anchor
          anchor_tail_stream_tail sizes burn anchor_long tail_long epoch] by blast
  have positive: "0 < W (tail_anchor_stream n m) (E*(n+m))"
    using reverse.tail_anchor_all_epochs_positive[OF tail_anchor_stream_tail
          tail_anchor_stream_anchor sizes burn anchor_long tail_long epoch] by blast
  show ?thesis using negative positive by blast
qed

end

theorem adam_persistent_epoch_inversion:
  assumes eta_positive: "0 < eta"
    and beta1_nonnegative: "0 \<le> beta1"
    and beta1_less_one: "beta1 < 1"
    and beta2_nonnegative: "0 \<le> beta2"
    and beta2_less_one: "beta2 < 1"
    and epsilon_positive: "0 < eps"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta1^J \<le> 1/6"
    and anchor_long: "real m*(eta/(eps*(1-beta1))) +
      real J*(eta/(eps*(1-beta1))) <
      real ((n-1)-J) * ((eta/(1+eps))/4)"
    and tail_long: "real n*(eta/(eps*(1-beta1))) +
      real J*(eta/(eps*(1-beta1))) <
      real ((m-1)-J) * ((eta/(1+eps))/4)"
    and epoch: "1 \<le> E"
  shows "aw_weight (aw_run eta beta1 beta2 eps 0
        (anchor_tail_stream n m) (E*(n+m))) < 0 \<and>
    0 < aw_weight (aw_run eta beta1 beta2 eps 0
        (tail_anchor_stream n m) (E*(n+m)))"
proof -
  interpret adam: aw_parameters eta beta1 beta2 eps 0
  proof (unfold_locales)
    show "0 < eta" by (rule eta_positive)
    show "0 \<le> beta1" by (rule beta1_nonnegative)
    show "beta1 < 1" by (rule beta1_less_one)
    show "0 \<le> beta2" by (rule beta2_nonnegative)
    show "beta2 < 1" by (rule beta2_less_one)
    show "0 < eps" by (rule epsilon_positive)
    show "(0::real) \<le> 0" by simp
    show "eta * 0 \<le> 1" by simp
  qed
  show ?thesis
    by (rule adam.adamw_persistent_epoch_inversion[OF sizes burn anchor_long
          tail_long epoch])
qed

corollary aw_persistent_epoch_metrics:
  assumes inversion: "aw_weight (aw_run eta beta1 beta2 eps decay
        (anchor_tail_stream n m) (E*(n+m))) < 0 \<and>
    0 < aw_weight (aw_run eta beta1 beta2 eps decay
        (tail_anchor_stream n m) (E*(n+m)))"
  shows "clean_test_risk p (aw_weight (aw_run eta beta1 beta2 eps decay
        (anchor_tail_stream n m) (E*(n+m)))) = 1-p \<and>
    clean_test_auc p (aw_weight (aw_run eta beta1 beta2 eps decay
        (anchor_tail_stream n m) (E*(n+m)))) = p \<and>
    clean_test_risk p (aw_weight (aw_run eta beta1 beta2 eps decay
        (tail_anchor_stream n m) (E*(n+m)))) = p \<and>
    clean_test_auc p (aw_weight (aw_run eta beta1 beta2 eps decay
        (tail_anchor_stream n m) (E*(n+m)))) = 1-p"
proof -
  have negative: "aw_weight (aw_run eta beta1 beta2 eps decay
      (anchor_tail_stream n m) (E*(n+m))) < 0" using inversion by blast
  have positive: "0 < aw_weight (aw_run eta beta1 beta2 eps decay
      (tail_anchor_stream n m) (E*(n+m)))" using inversion by blast
  show ?thesis using clean_test_risk_negative[OF negative]
    clean_test_auc_negative[OF negative]
    clean_test_risk_positive[OF positive]
    clean_test_auc_positive[OF positive] by blast
qed

end