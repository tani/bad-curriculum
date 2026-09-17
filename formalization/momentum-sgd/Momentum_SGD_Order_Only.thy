theory Momentum_SGD_Order_Only
  imports "../core/Order_Only_Inversion_Extensions"
begin

section \<open>Momentum stochastic gradient descent\<close>

text \<open>
  The pair contains the scalar logistic weight and the persistent velocity.
  Neither coordinate is reset at the Anchor--Tail boundary.
\<close>

definition momentum_sgd_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "momentum_sgd_state eta mu xs k = momentum_logistic_state eta mu xs k"

definition momentum_sgd_weight ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_sgd_weight eta mu xs k = fst (momentum_sgd_state eta mu xs k)"

definition momentum_sgd_velocity ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_sgd_velocity eta mu xs k = snd (momentum_sgd_state eta mu xs k)"

lemma momentum_sgd_initial [simp]:
  "momentum_sgd_state eta mu xs 0 = (0, 0)"
  by (simp add: momentum_sgd_state_def)

lemma momentum_sgd_step:
  "momentum_sgd_state eta mu xs (Suc k) =
    (let state = momentum_sgd_state eta mu xs k;
         gradient = sigmoid (fst state) - bool_value (xs ! k);
         velocity = mu * snd state + gradient
     in (fst state - eta * velocity, velocity))"
  by (simp add: momentum_sgd_state_def)

lemma momentum_sgd_weight_eq:
  "momentum_sgd_weight eta mu xs k = momentum_w_state eta mu xs k"
  by (simp add: momentum_sgd_weight_def momentum_sgd_state_def
      momentum_w_state_def)

lemma momentum_sgd_velocity_eq:
  "momentum_sgd_velocity eta mu xs k = momentum_v_state eta mu xs k"
  by (simp add: momentum_sgd_velocity_def momentum_sgd_state_def
      momentum_v_state_def)

theorem momentum_sgd_order_only_inversion:
  fixes eta mu q G_attack G_random epsilon :: real
  assumes eta_positive: "0 < eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
    and attack_reference:
      "binary_logistic_state (momentum_effective_step eta mu) q xs_attack N
        \<le> -G_attack"
    and random_reference:
      "G_random \<le> binary_logistic_state (momentum_effective_step eta mu) q
        xs_random N"
    and error_small:
      "momentum_transfer_error eta mu N < min G_attack G_random"
  shows "clean_test_risk epsilon
      (momentum_sgd_weight eta mu xs_attack N) = 1 - epsilon \<and>
    clean_test_risk epsilon
      (momentum_sgd_weight eta mu xs_random N) = epsilon \<and>
    clean_test_auc epsilon
      (momentum_sgd_weight eta mu xs_attack N) = epsilon \<and>
    clean_test_auc epsilon
      (momentum_sgd_weight eta mu xs_random N) = 1 - epsilon"
  unfolding momentum_sgd_weight_eq
  by (rule momentum_inversion_transfer[OF eta_positive mu_nonnegative
        mu_less_one effective_at_most_four attack_reference random_reference
        error_small])

theorem momentum_sgd_attack_metric_limits:
  fixes mu :: real
  assumes "0 \<le> mu" "mu < 1"
  shows "((\<lambda>k.
    (clean_test_risk (curriculum_tail_ratio k)
      (momentum_sgd_weight (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)),
     clean_test_auc (curriculum_tail_ratio k)
      (momentum_sgd_weight (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
  unfolding momentum_sgd_weight_eq
  by (rule curriculum_fixed_momentum_attack_metric_limits[OF assms])

end
