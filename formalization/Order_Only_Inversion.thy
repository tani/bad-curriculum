theory Order_Only_Inversion
  imports "HOL-Analysis.Convex"
begin

section \<open>Exact finite-step order-only inversion\<close>

text \<open>
  This theory formalizes the deterministic core of the supplied construction.
  It uses the exact one-dimensional logistic SGD updates, preserves the clean
  label rule @{term \<open>clean_label\<close>}, and proves that an Anchor-to-Tail schedule
  crosses a negative margin under an explicit finite-step takeover inequality.
  The companion theories formalize the uniform random-permutation model, the
  vanishing-tail asymptotic family, the realizable two-coordinate extension,
  momentum, and additive perturbation transfer.
\<close>

definition sigmoid :: "real \<Rightarrow> real" where
  "sigmoid x = 1 / (1 + exp (- x))"

definition anchor_step :: "real \<Rightarrow> real \<Rightarrow> real" where
  "anchor_step \<eta> w = w + \<eta> * sigmoid (- w)"

definition tail_step :: "real \<Rightarrow> real \<Rightarrow> real" where
  "tail_step \<eta> w = w - \<eta> * sigmoid w"

definition anchor_state :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "anchor_state \<eta> n = ((anchor_step \<eta>) ^^ n) 0"

definition attack_state :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "attack_state \<eta> n m = ((tail_step \<eta>) ^^ m) (anchor_state \<eta> n)"

lemma sigmoid_pos: "0 < sigmoid x"
proof -
  have "0 < 1 + exp (- x)"
    using exp_ge_zero[of "- x"] by linarith
  then show ?thesis
    unfolding sigmoid_def by (intro divide_pos_pos) simp_all
qed

lemma sigmoid_le_one: "sigmoid x \<le> 1"
proof -
  have h_denominator: "1 \<le> 1 + exp (- x)"
    using exp_ge_zero[of "- x"] by linarith
  have h_inverse: "inverse (1 + exp (- x)) \<le> inverse 1"
    using h_denominator by (rule le_imp_inverse_le) simp
  show ?thesis
    unfolding sigmoid_def
    using h_inverse by (simp add: divide_inverse)
qed

lemma tail_step_le:
  assumes "0 \<le> \<eta>"
  shows "tail_step \<eta> w \<le> w"
proof -
  have h_sigmoid: "0 \<le> sigmoid w"
    using sigmoid_pos[of w] by linarith
  have "0 \<le> \<eta> * sigmoid w"
    using assms h_sigmoid by (rule mult_nonneg_nonneg)
  then show ?thesis
    unfolding tail_step_def by linarith
qed

lemma tail_step_lt:
  assumes "0 < \<eta>"
  shows "tail_step \<eta> w < w"
  using assms sigmoid_pos by (simp add: tail_step_def)

lemma sigmoid_lower_bound:
  assumes "- \<gamma> \<le> w"
  shows "1 / (1 + exp \<gamma>) \<le> sigmoid w"
proof -
  have h_exp: "exp (- w) \<le> exp \<gamma>"
    using assms by (intro exp_mono) linarith
  have h_exp_nonneg: "0 \<le> exp (- w)"
    by (rule exp_ge_zero)
  have h_pos_left: "0 < 1 + exp (- w)"
    using h_exp_nonneg by linarith
  have h_denominator: "1 + exp (- w) \<le> 1 + exp \<gamma>"
    using h_exp by linarith
  have h_inverse: "inverse (1 + exp \<gamma>) \<le> inverse (1 + exp (- w))"
    using h_denominator h_pos_left by (rule le_imp_inverse_le)
  show ?thesis
    unfolding sigmoid_def
    using h_inverse by (simp add: divide_inverse)
qed

lemma tail_step_decreases_at_least:
  assumes "0 < \<eta>" and "- \<gamma> \<le> w"
  shows "tail_step \<eta> w \<le> w - \<eta> * (1 / (1 + exp \<gamma>))"
proof -
  have h_sigmoid: "1 / (1 + exp \<gamma>) \<le> sigmoid w"
    using assms(2) by (rule sigmoid_lower_bound)
  have h_scaled: "\<eta> * (1 / (1 + exp \<gamma>)) \<le> \<eta> * sigmoid w"
    by (rule mult_left_mono [OF h_sigmoid]) (use assms in linarith)
  show ?thesis
    unfolding tail_step_def
    using h_scaled by linarith
qed

lemma iterate_cross_or_bound:
  fixes F :: "real \<Rightarrow> real"
  assumes decrease: "\<And>x. F x \<le> x"
    and descent: "\<And>x. - \<gamma> \<le> x \<Longrightarrow> F x \<le> x - d"
  shows "(F ^^ m) w < - \<gamma> \<or> (F ^^ m) w \<le> w - real m * d"
  using decrease descent
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "(F ^^ m) w < - \<gamma>")
    case True
    then have "F ((F ^^ m) w) < - \<gamma>"
      using decrease[of "(F ^^ m) w"] by linarith
    then show ?thesis by (simp add: funpow_Suc_right)
  next
    case False
    have h_lower: "- \<gamma> \<le> (F ^^ m) w"
      using False by linarith
    have h_bound: "(F ^^ m) w \<le> w - real m * d"
      using Suc.IH decrease descent False by blast
    have h_descent: "F ((F ^^ m) w) \<le> (F ^^ m) w - d"
      using descent h_lower by blast
    have "F ((F ^^ m) w) \<le> w - real (Suc m) * d"
    proof -
      have "F ((F ^^ m) w) \<le> (w - real m * d) - d"
        using h_bound h_descent by linarith
      also have "(w - real m * d) - d = w - real (Suc m) * d"
        by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    then show ?thesis by (simp add: funpow_Suc_right)
  qed
qed

theorem tail_crosses_from_upper_bound:
  assumes \<eta>_pos: "0 < \<eta>"
    and start_bound: "w \<le> h"
    and takeover: "h - real m * (\<eta> * (1 / (1 + exp \<gamma>))) < - \<gamma>"
  shows "((tail_step \<eta>) ^^ m) w < - \<gamma>"
proof -
  have h_decrease: "\<And>x. tail_step \<eta> x \<le> x"
  proof -
    fix x
    have \<eta>_nonneg: "0 \<le> \<eta>"
      using \<eta>_pos by linarith
    show "tail_step \<eta> x \<le> x"
      using \<eta>_nonneg by (rule tail_step_le)
  qed
  have h_descent: "\<And>x. - \<gamma> \<le> x \<Longrightarrow> tail_step \<eta> x \<le> x - \<eta> * (1 / (1 + exp \<gamma>))"
    using \<eta>_pos by (rule tail_step_decreases_at_least)
  have h_cases:
      "((tail_step \<eta>) ^^ m) w < - \<gamma> \<or>
       ((tail_step \<eta>) ^^ m) w \<le> w - real m * (\<eta> * (1 / (1 + exp \<gamma>)))"
    using iterate_cross_or_bound[of "tail_step \<eta>" \<gamma> "\<eta> * (1 / (1 + exp \<gamma>))" m w]
      h_decrease h_descent
    by blast
  then show ?thesis
  proof
    assume "((tail_step \<eta>) ^^ m) w < - \<gamma>"
    then show ?thesis .
  next
    assume h_tail: "((tail_step \<eta>) ^^ m) w \<le> w - real m * (\<eta> * (1 / (1 + exp \<gamma>)))"
    show ?thesis
      using h_tail start_bound takeover by linarith
  qed
qed

corollary anchor_tail_inversion:
  assumes "0 < \<eta>"
    and "anchor_state \<eta> n \<le> h"
    and "h - real m * (\<eta> * (1 / (1 + exp \<gamma>))) < - \<gamma>"
  shows "attack_state \<eta> n m < - \<gamma>"
  unfolding attack_state_def
  using assms by (rule tail_crosses_from_upper_bound)

corollary logarithmic_anchor_bound_implies_inversion:
  assumes "0 < \<eta>"
    and "anchor_state \<eta> n \<le> ln (1 + real n * (exp \<eta> - 1))"
    and "ln (1 + real n * (exp \<eta> - 1))
         - real m * (\<eta> * (1 / (1 + exp \<gamma>))) < - \<gamma>"
  shows "attack_state \<eta> n m < - \<gamma>"
  using assms by (rule anchor_tail_inversion)

section \<open>Clean labels and pointwise classification reversal\<close>

definition clean_label :: "real \<Rightarrow> real \<Rightarrow> real" where
  "clean_label s t = s * t"

definition prediction :: "real \<Rightarrow> real \<Rightarrow> real" where
  "prediction w s = (if 0 \<le> w * s then 1 else - 1)"

lemma anchor_label: "clean_label s 1 = s"
  by (simp add: clean_label_def)

lemma counterexample_tail_label: "clean_label s (-1) = - s"
  by (simp add: clean_label_def)

lemma prediction_positive:
  assumes "0 < w" and "s = 1 \<or> s = -1"
  shows "prediction w s = s"
  using assms
  unfolding prediction_def
  by auto

lemma prediction_negative:
  assumes "w < 0" and "s = 1 \<or> s = -1"
  shows "prediction w s = - s"
  using assms
  unfolding prediction_def
  by auto

theorem anchor_tail_flips_anchor_examples:
  assumes "0 < \<eta>"
    and "0 < \<gamma>"
    and "anchor_state \<eta> n \<le> h"
    and "h - real m * (\<eta> * (1 / (1 + exp \<gamma>))) < - \<gamma>"
    and "s = 1 \<or> s = -1"
  shows "prediction (attack_state \<eta> n m) s \<noteq> clean_label s 1"
proof -
  have h_attack: "attack_state \<eta> n m < - \<gamma>"
    using assms(1) assms(3) assms(4) by (rule anchor_tail_inversion)
  have h_negative: "attack_state \<eta> n m < 0"
    using h_attack assms(2) by linarith
  have h_prediction: "prediction (attack_state \<eta> n m) s = - s"
    using prediction_negative h_negative assms(5) by blast
  show ?thesis
    using h_prediction assms(5) by (auto simp: clean_label_def)
qed

lemma exp_secant:
  fixes u eta :: real
  assumes "0 \<le> u" and "u \<le> 1"
  shows "exp (u * eta) \<le> 1 + u * (exp eta - 1)"
proof -
  note h = convex_onD[OF exp_convex, where t=u and x="0::real" and y=eta]
  show ?thesis using h assms by (simp add: algebra_simps)
qed

lemma sigmoid_lt_one: "sigmoid x < 1"
proof -
  have exponential_positive: "0 < exp (- x)" by (simp add: order_less_le)
  have denominator_greater_one: "1 < 1 + exp (- x)"
    using exponential_positive by linarith
  have "1 / (1 + exp (- x)) < (1::real) / 1"
    by (rule frac_less2) (use denominator_greater_one in simp_all)
  then show ?thesis unfolding sigmoid_def by simp
qed

lemma anchor_step_gt:
  assumes "0 < eta"
  shows "w < anchor_step eta w"
proof -
  have "0 < eta * sigmoid (- w)"
    using assms sigmoid_pos by (rule mult_pos_pos)
  then show ?thesis unfolding anchor_step_def by linarith
qed

lemma anchor_exp_step_bound:
  assumes "0 \<le> eta"
  shows "exp (anchor_step eta w) \<le> exp w + (exp eta - 1)"
proof -
  define u where "u = 1 / (1 + exp w)"
  have exponential_positive: "0 < exp w" by (simp add: order_less_le)
  have denominator_positive: "0 < 1 + exp w"
    using exponential_positive by linarith
  have u_nonnegative: "0 \<le> u"
    unfolding u_def using denominator_positive
    by (intro divide_nonneg_nonneg) simp_all
  have u_at_most_one: "u \<le> 1"
  proof -
    have "1 / (1 + exp w) \<le> (1::real) / 1"
      by (rule frac_le) (use exponential_positive in simp_all)
    then show ?thesis unfolding u_def by simp
  qed
  have secant: "exp (u * eta) \<le> 1 + u * (exp eta - 1)"
    using exp_secant[OF u_nonnegative u_at_most_one, of eta] .
  have exp_eta_nonnegative: "0 \<le> exp eta - 1" using assms by simp
  have ratio: "exp w * u \<le> 1"
  proof -
    have "exp w / (1 + exp w) \<le> (1 + exp w) / (1 + exp w)"
    proof (rule divide_right_mono)
      show "exp w \<le> 1 + exp w" using exponential_positive by linarith
      show "0 \<le> 1 + exp w" using denominator_positive by linarith
    qed
    also have "\<dots> = 1" using denominator_positive by simp
    finally show ?thesis unfolding u_def by (simp add: divide_inverse)
  qed
  have scaled: "exp w * u * (exp eta - 1) \<le> exp eta - 1"
    using mult_right_mono[OF ratio exp_eta_nonnegative] by simp
  have "exp (anchor_step eta w) = exp w * exp (u * eta)"
    unfolding anchor_step_def sigmoid_def u_def
    by (simp add: exp_add mult.commute)
  also have "\<dots> \<le> exp w * (1 + u * (exp eta - 1))"
    using secant exp_ge_zero by (intro mult_left_mono)
  also have "\<dots> \<le> exp w + (exp eta - 1)"
    using scaled by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma anchor_exp_bound:
  assumes "0 \<le> eta"
  shows "exp (anchor_state eta n) \<le> 1 + real n * (exp eta - 1)"
proof (induction n)
  case 0
  show ?case by (simp add: anchor_state_def)
next
  case (Suc n)
  have "exp (anchor_state eta (Suc n)) =
      exp (anchor_step eta (anchor_state eta n))"
    by (simp add: anchor_state_def funpow_Suc_right)
  also have "\<dots> \<le> exp (anchor_state eta n) + (exp eta - 1)"
    using anchor_exp_step_bound[OF assms] .
  also have "\<dots> \<le> (1 + real n * (exp eta - 1)) + (exp eta - 1)"
    using Suc.IH by linarith
  also have "\<dots> = 1 + real (Suc n) * (exp eta - 1)"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma anchor_state_nonnegative:
  assumes "0 \<le> eta"
  shows "0 \<le> anchor_state eta n"
proof (induction n)
  case 0
  show ?case by (simp add: anchor_state_def)
next
  case (Suc n)
  have sigmoid_nonnegative: "0 \<le> sigmoid (- anchor_state eta n)"
    using sigmoid_pos[of "- anchor_state eta n"] by linarith
  have increment_nonnegative: "0 \<le> eta * sigmoid (- anchor_state eta n)"
    using assms sigmoid_nonnegative by (rule mult_nonneg_nonneg)
  have "anchor_state eta n \<le> anchor_step eta (anchor_state eta n)"
    unfolding anchor_step_def using increment_nonnegative by linarith
  with Suc.IH show ?case
    by (simp add: anchor_state_def funpow_Suc_right)
qed

lemma anchor_state_positive:
  assumes "0 < eta" and "0 < n"
  shows "0 < anchor_state eta n"
proof -
  obtain k where n: "n = Suc k" using assms(2) by (cases n) auto
  have nonnegative: "0 \<le> anchor_state eta k"
    using anchor_state_nonnegative[of eta k] assms(1) by linarith
  have "anchor_state eta k < anchor_step eta (anchor_state eta k)"
    using anchor_step_gt assms(1) .
  with nonnegative show ?thesis
    by (simp add: n anchor_state_def funpow_Suc_right)
qed

lemma anchor_log_bound:
  assumes "0 \<le> eta"
  shows "anchor_state eta n \<le> ln (1 + real n * (exp eta - 1))"
proof -
  have exp_eta_nonnegative: "0 \<le> exp eta - 1" using assms by simp
  have product_nonnegative: "0 \<le> real n * (exp eta - 1)"
    using exp_eta_nonnegative by (intro mult_nonneg_nonneg) simp_all
  have rhs_positive: "0 < 1 + real n * (exp eta - 1)"
    using product_nonnegative by linarith
  have "exp (anchor_state eta n) \<le> 1 + real n * (exp eta - 1)"
    using anchor_exp_bound[OF assms] .
  also have "\<dots> = exp (ln (1 + real n * (exp eta - 1)))"
    using rhs_positive by simp
  finally show ?thesis by simp
qed

end
