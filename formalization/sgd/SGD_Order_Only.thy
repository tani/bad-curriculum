theory SGD_Order_Only
  imports "../core/Order_Only_Inversion_Extensions"
begin

section \<open>Plain stochastic gradient descent\<close>

text \<open>
  The state below is the exact scalar logistic SGD update used by the
  experiment.  The Boolean presentation stream is the only varying input.
\<close>

primrec sgd_state :: "real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "sgd_state eta xs 0 = 0"
| "sgd_state eta xs (Suc k) =
    sgd_state eta xs k +
      eta * (bool_value (xs ! k) - sigmoid (sgd_state eta xs k))"

lemma sgd_state_eq_binary_logistic_state:
  "sgd_state eta xs k = binary_logistic_state eta q xs k"
proof (induction k)
  case 0
  then show ?case
    unfolding binary_logistic_state_def perturbed_iteration_def by simp
next
  case (Suc k)
  then show ?case by (simp add: binary_logistic_state_Suc)
qed

lemma sgd_attack_order_exact:
  "sgd_state eta (attack_order n m) (n + m) = attack_state eta n m"
proof -
  have "sgd_state eta (attack_order n m) (n + m) =
      binary_logistic_state eta 0 (attack_order n m) (n + m)"
    by (rule sgd_state_eq_binary_logistic_state)
  also have "... = attack_state eta n m"
    by (rule binary_logistic_state_attack_order)
  finally show ?thesis .
qed

theorem sgd_anchor_tail_inversion:
  assumes eta_positive: "0 < eta"
    and anchor_bound: "anchor_state eta n \<le> h"
    and takeover:
      "h - real m * (eta * (1 / (1 + exp gamma))) < - gamma"
  shows "sgd_state eta (attack_order n m) (n + m) < - gamma"
proof -
  have "attack_state eta n m < - gamma"
    by (rule anchor_tail_inversion[OF eta_positive anchor_bound takeover])
  then show ?thesis by (simp add: sgd_attack_order_exact)
qed

corollary sgd_attack_metrics:
  assumes eta_positive: "0 < eta"
    and anchor_bound: "anchor_state eta n \<le> h"
    and takeover:
      "h - real m * (eta * (1 / (1 + exp gamma))) < - gamma"
    and gamma_positive: "0 < gamma"
  shows "clean_test_risk p (sgd_state eta (attack_order n m) (n + m)) = 1 - p"
    and "clean_test_auc p (sgd_state eta (attack_order n m) (n + m)) = p"
proof -
  have negative: "sgd_state eta (attack_order n m) (n + m) < 0"
    using sgd_anchor_tail_inversion[OF eta_positive anchor_bound takeover]
      gamma_positive by linarith
  show "clean_test_risk p (sgd_state eta (attack_order n m) (n + m)) = 1 - p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p (sgd_state eta (attack_order n m) (n + m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

end
