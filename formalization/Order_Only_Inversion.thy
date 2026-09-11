theory Order_Only_Inversion
  imports "HOL-Analysis.Convex"
begin

section \<open>Exact finite-step order-only inversion\<close>

text \<open>
  This theory formalizes the deterministic core of the supplied construction.
  It uses the exact one-dimensional logistic SGD updates, preserves the clean
  label rule @{term \<open>clean_label\<close>}, and proves that an Anchor-to-Tail schedule
  crosses a negative margin under an explicit finite-step takeover inequality.
  The probability model for a random permutation, the asymptotic family, the
  realizable two-coordinate extension, and momentum require separate
  probability and perturbation developments and are not asserted here.
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

end
