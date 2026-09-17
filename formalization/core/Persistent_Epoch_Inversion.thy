theory Persistent_Epoch_Inversion
  imports Order_Only_Inversion_Extensions
begin

section \<open>Persistent-state optimizer contract\<close>

text \<open>The effective step may depend on the complete preceding history.  The
first-moment state and the global clock are never reset between blocks.\<close>

locale persistent_update =
  fixes beta rho amin S :: real
    and a :: "nat \<Rightarrow> real"
    and label :: "nat \<Rightarrow> bool"
    and weight moment :: "nat \<Rightarrow> real"
  assumes beta_nonnegative: "0 \<le> beta"
    and beta_less_one: "beta < 1"
    and rho_nonnegative: "0 \<le> rho"
    and rho_at_most_one: "rho \<le> 1"
    and amin_positive: "0 < amin"
    and step_lower: "\<And>k. amin \<le> a (Suc k)"
    and step_upper: "\<And>k. a (Suc k) \<le> S"
    and weight_initial [simp]: "weight 0 = 0"
    and moment_initial [simp]: "moment 0 = 0"
    and moment_rec: "\<And>k. moment (Suc k) = beta * moment k +
      (1-beta) * (sigmoid (weight k) - bool_value (label k))"
    and weight_rec: "\<And>k. weight (Suc k) =
      rho * weight k - a (Suc k) * moment (Suc k)"
begin

lemma beta_at_most_one: "beta \<le> 1"
  using beta_less_one by linarith

lemma one_minus_beta_nonnegative: "0 \<le> 1-beta"
  using beta_less_one by linarith

lemma step_nonnegative: "0 \<le> a (Suc k)"
  using step_lower[of k] amin_positive by linarith

lemma S_positive: "0 < S"
  using amin_positive step_lower[of 0] step_upper[of 0] by linarith

lemma moment_abs_le_one: "abs (moment k) \<le> 1"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have gradient: "abs (sigmoid (weight k) - bool_value (label k)) \<le> 1"
    by (rule binary_logistic_gradient_abs_le_one)
  have triangle: "abs (moment (Suc k)) \<le>
      beta * abs (moment k) + (1-beta) *
        abs (sigmoid (weight k) - bool_value (label k))"
    unfolding moment_rec
    using abs_triangle_ineq[of "beta * moment k"
        "(1-beta) * (sigmoid (weight k) - bool_value (label k))"]
      beta_nonnegative one_minus_beta_nonnegative
    by (simp add: abs_mult)
  have first: "beta * abs (moment k) \<le> beta"
    using mult_left_mono[OF Suc.IH beta_nonnegative] by simp
  have second: "(1-beta) *
      abs (sigmoid (weight k) - bool_value (label k)) \<le> 1-beta"
    using mult_left_mono[OF gradient one_minus_beta_nonnegative] by simp
  show ?case using triangle first second by linarith
qed

lemma moment_bounds: "-1 \<le> moment k" "moment k \<le> 1"
  using moment_abs_le_one[of k] by (simp_all add: abs_le_iff)

lemma scaled_moment_abs: "abs (a (Suc k) * moment (Suc k)) \<le> S"
proof -
  have "abs (a (Suc k) * moment (Suc k)) =
      a (Suc k) * abs (moment (Suc k))"
    using step_nonnegative[of k] by (simp add: abs_mult)
  also have "... \<le> a (Suc k) * 1"
    using mult_left_mono[OF moment_abs_le_one[of "Suc k"] step_nonnegative[of k]] by simp
  also have "... \<le> S" using step_upper[of k] by simp
  finally show ?thesis .
qed

lemma rho_weight_upper: "rho * x \<le> max x 0"
proof (cases "0 \<le> x")
  case True
  then show ?thesis using mult_right_mono[OF rho_at_most_one True] by simp
next
  case False
  have "rho * x \<le> 0"
    by (rule mult_nonneg_nonpos) (use rho_nonnegative False in auto)
  then show ?thesis using False by simp
qed

lemma rho_weight_lower: "min x 0 \<le> rho * x"
proof (cases "0 \<le> x")
  case True
  have "0 \<le> rho * x"
    by (rule mult_nonneg_nonneg[OF rho_nonnegative True])
  then show ?thesis using True by simp
next
  case False
  have product: "0 \<le> (1-rho) * (-x)"
    by (rule mult_nonneg_nonneg) (use rho_at_most_one False in auto)
  have identity: "rho * x - x = (1-rho) * (-x)" by algebra
  then have "x \<le> rho * x" using product by linarith
  then show ?thesis using False by simp
qed

lemma weight_step_upper: "weight (Suc k) \<le> max (weight k) 0 + S"
proof -
  have direction: "-S \<le> a (Suc k) * moment (Suc k)"
    using scaled_moment_abs[of k] by (simp add: abs_le_iff)
  show ?thesis unfolding weight_rec
    using rho_weight_upper[of "weight k"] direction by linarith
qed

lemma weight_step_lower: "min (weight k) 0 - S \<le> weight (Suc k)"
proof -
  have direction: "a (Suc k) * moment (Suc k) \<le> S"
    using scaled_moment_abs[of k] by (simp add: abs_le_iff)
  show ?thesis unfolding weight_rec
    using rho_weight_lower[of "weight k"] direction by linarith
qed

lemma tail_negative_step:
  assumes tail: "\<not> label k" and wneg: "weight k < 0"
    and mpos: "0 < moment k"
  shows "weight (Suc k) < 0 \<and> 0 < moment (Suc k)"
proof -
  have gp: "0 < sigmoid (weight k) - bool_value (label k)"
    using sigmoid_pos[of "weight k"] tail by (simp add: bool_value_def)
  have old_nonnegative: "0 \<le> beta * moment k"
    by (rule mult_nonneg_nonneg) (use beta_nonnegative mpos in auto)
  have fresh_positive: "0 < (1-beta) *
      (sigmoid (weight k) - bool_value (label k))"
    by (rule mult_pos_pos) (use beta_less_one gp in auto)
  have next_m: "0 < moment (Suc k)"
    unfolding moment_rec using old_nonnegative fresh_positive by linarith
  have contracted: "rho * weight k \<le> 0"
    by (rule mult_nonneg_nonpos) (use rho_nonnegative wneg in auto)
  have step_positive: "0 < a (Suc k)"
    using step_lower[of k] amin_positive by linarith
  have descent: "0 < a (Suc k) * moment (Suc k)"
    by (rule mult_pos_pos[OF step_positive next_m])
  have next_w: "weight (Suc k) < 0"
    unfolding weight_rec using contracted descent by linarith
  show ?thesis using next_w next_m by blast
qed

lemma tail_crossing_positive_moment:
  assumes tail: "\<not> label k" and wnonneg: "0 \<le> weight k"
    and next_negative: "weight (Suc k) < 0"
  shows "0 < moment (Suc k)"
proof (rule ccontr)
  assume not_positive: "\<not> 0 < moment (Suc k)"
  have moment_nonpositive: "moment (Suc k) \<le> 0"
    using not_positive by linarith
  have direction: "a (Suc k) * moment (Suc k) \<le> 0"
    by (rule mult_nonneg_nonpos[OF step_nonnegative moment_nonpositive])
  have contracted: "0 \<le> rho * weight k"
    by (rule mult_nonneg_nonneg[OF rho_nonnegative wnonneg])
  have rec: "weight (Suc k) = rho * weight k - a (Suc k) * moment (Suc k)"
    by (rule weight_rec)
  show False using next_negative contracted direction rec by linarith
qed

lemma anchor_positive_step:
  assumes anchor: "label k" and wpos: "0 < weight k"
    and mneg: "moment k < 0"
  shows "0 < weight (Suc k) \<and> moment (Suc k) < 0"
proof -
  have gn: "sigmoid (weight k) - bool_value (label k) < 0"
    using sigmoid_pos[of "- weight k"] anchor
    by (simp add: bool_value_def sigmoid_neg_identity)
  have old_nonpositive: "beta * moment k \<le> 0"
    by (rule mult_nonneg_nonpos) (use beta_nonnegative mneg in auto)
  have fresh_negative: "(1-beta) *
      (sigmoid (weight k) - bool_value (label k)) < 0"
    by (rule mult_pos_neg) (use beta_less_one gn in auto)
  have next_m: "moment (Suc k) < 0"
    unfolding moment_rec using old_nonpositive fresh_negative by linarith
  have contracted: "0 \<le> rho * weight k"
    by (rule mult_nonneg_nonneg) (use rho_nonnegative wpos in auto)
  have step_positive: "0 < a (Suc k)"
    using step_lower[of k] amin_positive by linarith
  have ascent: "a (Suc k) * moment (Suc k) < 0"
    by (rule mult_pos_neg[OF step_positive next_m])
  have next_w: "0 < weight (Suc k)"
    unfolding weight_rec using contracted ascent by linarith
  show ?thesis using next_w next_m by blast
qed

lemma anchor_crossing_negative_moment:
  assumes anchor: "label k" and wnonpos: "weight k \<le> 0"
    and next_positive: "0 < weight (Suc k)"
  shows "moment (Suc k) < 0"
proof (rule ccontr)
  assume not_negative: "\<not> moment (Suc k) < 0"
  have moment_nonnegative: "0 \<le> moment (Suc k)"
    using not_negative by linarith
  have direction: "0 \<le> a (Suc k) * moment (Suc k)"
    by (rule mult_nonneg_nonneg[OF step_nonnegative moment_nonnegative])
  have contracted: "rho * weight k \<le> 0"
    by (rule mult_nonneg_nonpos[OF rho_nonnegative wnonpos])
  have rec: "weight (Suc k) = rho * weight k - a (Suc k) * moment (Suc k)"
    by (rule weight_rec)
  show False using next_positive contracted direction rec by linarith
qed

section \<open>Persistent sign regions and burn-in\<close>

lemma beta_power_bounds: "0 \<le> beta^k \<and> beta^k \<le> 1"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have lower: "0 \<le> beta * beta^k"
    by (rule mult_nonneg_nonneg) (use beta_nonnegative Suc.IH in auto)
  have upper: "beta * beta^k \<le> beta * 1"
    by (rule mult_left_mono) (use beta_nonnegative Suc.IH in auto)
  show ?case
  proof
    show "0 \<le> beta^Suc k" using lower by (simp only: power_Suc)
    show "beta^Suc k \<le> 1" using upper beta_at_most_one
      by (simp only: power_Suc)
  qed
qed

lemma beta_power_antimono:
  assumes "i \<le> j"
  shows "beta^j \<le> beta^i"
proof -
  have split: "beta^j = beta^i * beta^(j-i)"
    using assms by (simp flip: power_add)
  have left_nonnegative: "0 \<le> beta^i" using beta_power_bounds by blast
  have right_at_most_one: "beta^(j-i) \<le> 1" using beta_power_bounds by blast
  have "beta^i * beta^(j-i) \<le> beta^i * 1"
    by (rule mult_left_mono[OF right_at_most_one left_nonnegative])
  then show ?thesis unfolding split by simp
qed

lemma affine_iteration_upper:
  fixes f :: "nat \<Rightarrow> real"
  assumes step: "\<And>i. i < n \<Longrightarrow> f (Suc i) \<le> f i + d"
  shows "f n \<le> f 0 + real n * d"
  using step
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "f n \<le> f 0 + real n * d"
    by (rule Suc.IH) (use Suc.prems in auto)
  have step_n: "f (Suc n) \<le> f n + d" by (rule Suc.prems) simp
  have count: "real (Suc n) * d = real n * d + d"
    by (simp add: algebra_simps)
  show ?case using ih step_n count by linarith
qed
lemma affine_iteration_lower:
  fixes f :: "nat \<Rightarrow> real"
  assumes step: "\<And>i. i < n \<Longrightarrow> f i - d \<le> f (Suc i)"
  shows "f 0 - real n * d \<le> f n"
proof -
  have "(\<lambda>i. - f i) n \<le> (\<lambda>i. - f i) 0 + real n * d"
  proof (rule affine_iteration_upper)
    fix i
    assume "i < n"
    then have "f i - d \<le> f (Suc i)" by (rule step)
    then show "- f (Suc i) \<le> - f i + d" by linarith
  qed
  then show ?thesis by simp
qed

lemma tail_negative_has_positive_moment:
  assumes start: "0 \<le> weight s"
    and tail: "\<And>i. i < j \<Longrightarrow> \<not> label (s+i)"
    and negative: "weight (s+j) < 0"
  shows "0 < moment (s+j)"
  using tail negative
proof (induction j)
  case 0
  then show ?case using start by simp
next
  case (Suc j)
  show ?case
  proof (cases "weight (s+j) < 0")
    case True
    have mp: "0 < moment (s+j)"
      by (rule Suc.IH) (use Suc.prems True in auto)
    have lab: "\<not> label (s+j)" by (rule Suc.prems(1)) simp
    have step: "weight (Suc (s+j)) < 0 \<and> 0 < moment (Suc (s+j))"
      by (rule tail_negative_step[OF lab True mp])
    show ?thesis using step by simp
  next
    case False
    have wnonnegative: "0 \<le> weight (s+j)" using False by linarith
    have lab: "\<not> label (s+j)" by (rule Suc.prems(1)) simp
    show ?thesis
      using tail_crossing_positive_moment[OF lab wnonnegative] Suc.prems(2) by simp
  qed
qed

lemma tail_all_nonnegative:
  assumes start: "0 \<le> weight s"
    and tail: "\<And>i. i < K \<Longrightarrow> \<not> label (s+i)"
    and final: "0 \<le> weight (s+K)"
  shows "\<forall>j\<le>K. 0 \<le> weight (s+j)"
  using tail final
proof (induction K)
  case 0
  then show ?case using start by simp
next
  case (Suc K)
  have previous: "0 \<le> weight (s+K)"
  proof (rule ccontr)
    assume "\<not> 0 \<le> weight (s+K)"
    then have negative: "weight (s+K) < 0" by linarith
    have positive_moment: "0 < moment (s+K)"
      by (rule tail_negative_has_positive_moment[OF start _ negative])
        (use Suc.prems in auto)
    have lab: "\<not> label (s+K)" by (rule Suc.prems(1)) simp
    have "weight (Suc (s+K)) < 0"
      using tail_negative_step[OF lab negative positive_moment] by blast
    then show False using Suc.prems(2) by simp
  qed
  have ih: "\<forall>j\<le>K. 0 \<le> weight (s+j)"
    by (rule Suc.IH) (use Suc.prems previous in auto)
  show ?case using ih Suc.prems(2) by (metis le_Suc_eq)
qed

lemma anchor_positive_has_negative_moment:
  assumes start: "weight s \<le> 0"
    and anchor: "\<And>i. i < j \<Longrightarrow> label (s+i)"
    and positive: "0 < weight (s+j)"
  shows "moment (s+j) < 0"
  using anchor positive
proof (induction j)
  case 0
  then show ?case using start by simp
next
  case (Suc j)
  show ?case
  proof (cases "0 < weight (s+j)")
    case True
    have mn: "moment (s+j) < 0"
      by (rule Suc.IH) (use Suc.prems True in auto)
    have lab: "label (s+j)" by (rule Suc.prems(1)) simp
    have step: "0 < weight (Suc (s+j)) \<and> moment (Suc (s+j)) < 0"
      by (rule anchor_positive_step[OF lab True mn])
    show ?thesis using step by simp
  next
    case False
    have wnonpositive: "weight (s+j) \<le> 0" using False by linarith
    have lab: "label (s+j)" by (rule Suc.prems(1)) simp
    show ?thesis
      using anchor_crossing_negative_moment[OF lab wnonpositive] Suc.prems(2) by simp
  qed
qed

lemma anchor_all_nonpositive:
  assumes start: "weight s \<le> 0"
    and anchor: "\<And>i. i < K \<Longrightarrow> label (s+i)"
    and final: "weight (s+K) \<le> 0"
  shows "\<forall>j\<le>K. weight (s+j) \<le> 0"
  using anchor final
proof (induction K)
  case 0
  then show ?case using start by simp
next
  case (Suc K)
  have previous: "weight (s+K) \<le> 0"
  proof (rule ccontr)
    assume "\<not> weight (s+K) \<le> 0"
    then have positive: "0 < weight (s+K)" by linarith
    have negative_moment: "moment (s+K) < 0"
      by (rule anchor_positive_has_negative_moment[OF start _ positive])
        (use Suc.prems in auto)
    have lab: "label (s+K)" by (rule Suc.prems(1)) simp
    have "0 < weight (Suc (s+K))"
      using anchor_positive_step[OF lab positive negative_moment] by blast
    then show False using Suc.prems(2) by simp
  qed
  have ih: "\<forall>j\<le>K. weight (s+j) \<le> 0"
    by (rule Suc.IH) (use Suc.prems previous in auto)
  show ?case using ih Suc.prems(2) by (metis le_Suc_eq)
qed

lemma tail_moment_lower:
  assumes tail: "\<And>i. i < j \<Longrightarrow> \<not> label (s+i)"
    and nonnegative: "\<And>i. i < j \<Longrightarrow> 0 \<le> weight (s+i)"
  shows "1/2 - (3/2)*beta^j \<le> moment (s+j)"
  using tail nonnegative
proof (induction j)
  case 0
  have "-1 \<le> moment s" by (rule moment_bounds(1))
  then show ?case by simp
next
  case (Suc j)
  have ih: "1/2 - (3/2)*beta^j \<le> moment (s+j)"
    by (rule Suc.IH) (use Suc.prems in auto)
  have wn: "0 \<le> weight (s+j)" by (rule Suc.prems(2)) simp
  have lab: "\<not> label (s+j)" by (rule Suc.prems(1)) simp
  have gl: "1/2 \<le> sigmoid (weight (s+j)) - bool_value (label (s+j))"
    using sigmoid_lower_bound[of 0 "weight (s+j)"] wn lab
    by (simp add: bool_value_def sigmoid_def)
  have first: "beta * (1/2 - (3/2)*beta^j) \<le> beta * moment (s+j)"
    by (rule mult_left_mono[OF ih beta_nonnegative])
  have second: "(1-beta) * (1/2) \<le> (1-beta) *
      (sigmoid (weight (s+j)) - bool_value (label (s+j)))"
    by (rule mult_left_mono[OF gl one_minus_beta_nonnegative])
  have identity: "beta * (1/2 - (3/2)*beta^j) + (1-beta)*(1/2) =
      1/2 - (3/2)*beta^(Suc j)"
    by (simp only: power_Suc; algebra)
  show ?case unfolding add_Suc_right moment_rec
    using first second identity by linarith
qed

lemma anchor_moment_upper:
  assumes anchor: "\<And>i. i < j \<Longrightarrow> label (s+i)"
    and nonpositive: "\<And>i. i < j \<Longrightarrow> weight (s+i) \<le> 0"
  shows "moment (s+j) \<le> -1/2 + (3/2)*beta^j"
  using anchor nonpositive
proof (induction j)
  case 0
  have "moment s \<le> 1" by (rule moment_bounds(2))
  then show ?case by simp
next
  case (Suc j)
  have ih: "moment (s+j) \<le> -1/2 + (3/2)*beta^j"
    by (rule Suc.IH) (use Suc.prems in auto)
  have wn: "weight (s+j) \<le> 0" by (rule Suc.prems(2)) simp
  have lab: "label (s+j)" by (rule Suc.prems(1)) simp
  have gu: "sigmoid (weight (s+j)) - bool_value (label (s+j)) \<le> -1/2"
  proof -
    have "1/2 \<le> sigmoid (- weight (s+j))"
      using sigmoid_lower_bound[of 0 "- weight (s+j)"] wn by simp
    then show ?thesis using lab by (simp add: bool_value_def sigmoid_neg_identity)
  qed
  have first: "beta * moment (s+j) \<le> beta * (-1/2 + (3/2)*beta^j)"
    by (rule mult_left_mono[OF ih beta_nonnegative])
  have second: "(1-beta) *
      (sigmoid (weight (s+j)) - bool_value (label (s+j))) \<le> (1-beta)*(-1/2)"
    by (rule mult_left_mono[OF gu one_minus_beta_nonnegative])
  have identity: "beta * (-1/2 + (3/2)*beta^j) + (1-beta)*(-1/2) =
      -1/2 + (3/2)*beta^(Suc j)"
    by (simp only: power_Suc; algebra)
  show ?case unfolding add_Suc_right moment_rec
    using first second identity by linarith
qed

section \<open>Finite blocks reverse every carried state\<close>

lemma tail_quarter_descent:
  assumes nonnegative: "0 \<le> weight k"
    and quarter: "1/4 \<le> moment (Suc k)"
  shows "weight (Suc k) \<le> weight k - amin/4"
proof -
  have moment_nonnegative: "0 \<le> moment (Suc k)" using quarter by linarith
  have scale_step: "amin * moment (Suc k) \<le> a (Suc k) * moment (Suc k)"
    by (rule mult_right_mono[OF step_lower moment_nonnegative])
  have scale_quarter: "amin/4 \<le> amin * moment (Suc k)"
    using mult_left_mono[OF quarter, of amin] amin_positive by simp
  have contraction: "rho * weight k \<le> weight k"
    using rho_weight_upper[of "weight k"] nonnegative by simp
  have rec: "weight (Suc k) = rho * weight k - a (Suc k) * moment (Suc k)"
    by (rule weight_rec)
  show ?thesis using scale_step scale_quarter contraction rec by linarith
qed

lemma anchor_quarter_ascent:
  assumes nonpositive: "weight k \<le> 0"
    and quarter: "moment (Suc k) \<le> -1/4"
  shows "weight k + amin/4 \<le> weight (Suc k)"
proof -
  have neg_moment_nonnegative: "0 \<le> - moment (Suc k)" using quarter by linarith
  have scale_step: "amin * (- moment (Suc k)) \<le>
      a (Suc k) * (- moment (Suc k))"
    by (rule mult_right_mono[OF step_lower neg_moment_nonnegative])
  have scale_quarter: "amin/4 \<le> amin * (- moment (Suc k))"
    using mult_left_mono[of "1/4" "- moment (Suc k)" amin] quarter amin_positive
    by simp
  have contraction: "weight k \<le> rho * weight k"
    using rho_weight_lower[of "weight k"] nonpositive by simp
  have rec: "weight (Suc k) = rho * weight k - a (Suc k) * moment (Suc k)"
    by (rule weight_rec)
  show ?thesis using scale_step scale_quarter contraction rec by linarith
qed
lemma tail_block_crossing:
  assumes start: "0 \<le> weight s"
    and bounded: "weight s \<le> B"
    and tail: "\<And>i. i < K \<Longrightarrow> \<not> label (s+i)"
    and burn: "J \<le> K" "beta^J \<le> 1/6"
    and long: "B + real J*S < real (K-J) * (amin/4)"
  shows "weight (s+K) < 0 \<and> 0 < moment (s+K)"
proof -
  have negative: "weight (s+K) < 0"
  proof (rule ccontr)
    assume "\<not> weight (s+K) < 0"
    then have final: "0 \<le> weight (s+K)" by linarith
    have region: "\<forall>j\<le>K. 0 \<le> weight (s+j)"
      by (rule tail_all_nonnegative[OF start tail final])
have prefix: "weight (s+J) \<le> B + real J*S"
    proof -
      have raw: "(\<lambda>i. weight (s+i)) J \<le>
          (\<lambda>i. weight (s+i)) 0 + real J*S"
      proof (rule affine_iteration_upper)
        fix i
        assume less: "i < J"
        then have ik: "i < K" using burn(1) by linarith
        have wn: "0 \<le> weight (s+i)" using region ik by auto
        have "weight (Suc (s+i)) \<le> weight (s+i) + S"
          using weight_step_upper[of "s+i"] wn by simp
        then show "weight (s + Suc i) \<le> weight (s+i) + S" by simp
      qed
      have iter: "weight (s+J) \<le> weight s + real J*S" using raw by simp
      show ?thesis using iter bounded by linarith
    qed
    have quarter: "\<And>i. i < K-J \<Longrightarrow> 1/4 \<le> moment (s+J+Suc i)"
    proof -
      fix i
      assume less: "i < K-J"
      have index_le: "J + Suc i \<le> K" using burn(1) less by linarith
      have power: "beta^(J + Suc i) \<le> beta^J"
        by (rule beta_power_antimono) simp
      have moment_lower: "1/2 - (3/2)*beta^(J + Suc i) \<le>
          moment (s + (J + Suc i))"
      proof (rule tail_moment_lower)
        fix q
        assume qless: "q < J + Suc i"
        then have qK: "q < K" using index_le by linarith
        show "\<not> label (s+q)" by (rule tail[OF qK])
        show "0 \<le> weight (s+q)" using region qK by auto
      qed
      show "1/4 \<le> moment (s+J+Suc i)"
        using moment_lower power burn(2) by (simp add: add.assoc)
    qed
    have descent: "\<And>i. i < K-J \<Longrightarrow>
        weight (s+J+Suc i) \<le> weight (s+J+i) - amin/4"
    proof -
      fix i
      assume less: "i < K-J"
      have current: "J+i < K" using burn(1) less by linarith
      have wn: "0 \<le> weight (s+J+i)"
        using region current by (simp add: add.assoc)
      have qtr: "1/4 \<le> moment (Suc (s+J+i))"
        using quarter[OF less] by (simp add: add.assoc)
      have step: "weight (Suc (s+J+i)) \<le> weight (s+J+i) - amin/4"
        by (rule tail_quarter_descent[OF wn qtr])
      show "weight (s+J+Suc i) \<le> weight (s+J+i) - amin/4"
        using step by (simp add: add.assoc)
    qed
    have raw: "(\<lambda>i. weight (s+J+i)) (K-J) \<le>
        (\<lambda>i. weight (s+J+i)) 0 + real (K-J) * (-amin/4)"
    proof (rule affine_iteration_upper)
      fix i
      assume less: "i < K-J"
      show "weight (s+J+Suc i) \<le> weight (s+J+i) + -amin/4"
        using descent[OF less] by simp
    qed
    have iter: "weight (s+J+(K-J)) \<le>
        weight (s+J) + real (K-J) * (-amin/4)"
      using raw by simp    have endpoint: "weight (s+K) = weight (s+J+(K-J))"
      using burn(1) by simp
    show False using prefix iter long final endpoint by linarith
  qed
  have positive: "0 < moment (s+K)"
    by (rule tail_negative_has_positive_moment[OF start tail negative])
  show ?thesis using negative positive by blast
qed

lemma anchor_block_crossing:
  assumes start: "weight s \<le> 0"
    and bounded: "-B \<le> weight s"
    and anchor: "\<And>i. i < K \<Longrightarrow> label (s+i)"
    and burn: "J \<le> K" "beta^J \<le> 1/6"
    and long: "B + real J*S < real (K-J) * (amin/4)"
  shows "0 < weight (s+K) \<and> moment (s+K) < 0"
proof -
  have positive: "0 < weight (s+K)"
  proof (rule ccontr)
    assume "\<not> 0 < weight (s+K)"
    then have final: "weight (s+K) \<le> 0" by linarith
    have region: "\<forall>j\<le>K. weight (s+j) \<le> 0"
      by (rule anchor_all_nonpositive[OF start anchor final])
have prefix: "-B - real J*S \<le> weight (s+J)"
    proof -
      have raw: "(\<lambda>i. weight (s+i)) 0 - real J*S \<le>
          (\<lambda>i. weight (s+i)) J"
      proof (rule affine_iteration_lower)
        fix i
        assume less: "i < J"
        then have ik: "i < K" using burn(1) by linarith
        have wn: "weight (s+i) \<le> 0" using region ik by auto
        have "weight (s+i) - S \<le> weight (Suc (s+i))"
          using weight_step_lower[of "s+i"] wn by simp
        then show "weight (s+i) - S \<le> weight (s + Suc i)" by simp
      qed
      have iter: "weight s - real J*S \<le> weight (s+J)" using raw by simp
      show ?thesis using iter bounded by linarith
    qed
    have quarter: "\<And>i. i < K-J \<Longrightarrow> moment (s+J+Suc i) \<le> -1/4"
    proof -
      fix i
      assume less: "i < K-J"
      have index_le: "J + Suc i \<le> K" using burn(1) less by linarith
      have power: "beta^(J + Suc i) \<le> beta^J"
        by (rule beta_power_antimono) simp
      have moment_upper: "moment (s + (J + Suc i)) \<le>
          -1/2 + (3/2)*beta^(J + Suc i)"
      proof (rule anchor_moment_upper)
        fix q
        assume qless: "q < J + Suc i"
        then have qK: "q < K" using index_le by linarith
        show "label (s+q)" by (rule anchor[OF qK])
        show "weight (s+q) \<le> 0" using region qK by auto
      qed
      show "moment (s+J+Suc i) \<le> -1/4"
        using moment_upper power burn(2) by (simp add: add.assoc)
    qed
    have ascent: "\<And>i. i < K-J \<Longrightarrow>
        weight (s+J+i) + amin/4 \<le> weight (s+J+Suc i)"
    proof -
      fix i
      assume less: "i < K-J"
      have current: "J+i < K" using burn(1) less by linarith
      have wn: "weight (s+J+i) \<le> 0"
        using region current by (simp add: add.assoc)
      have qtr: "moment (Suc (s+J+i)) \<le> -1/4"
        using quarter[OF less] by (simp add: add.assoc)
      have step: "weight (s+J+i) + amin/4 \<le> weight (Suc (s+J+i))"
        by (rule anchor_quarter_ascent[OF wn qtr])
      show "weight (s+J+i) + amin/4 \<le> weight (s+J+Suc i)"
        using step by (simp add: add.assoc)
    qed
    have raw: "(\<lambda>i. weight (s+J+i)) 0 - real (K-J) * (-amin/4) \<le>
        (\<lambda>i. weight (s+J+i)) (K-J)"
    proof (rule affine_iteration_lower)
      fix i
      assume less: "i < K-J"
      show "weight (s+J+i) - -amin/4 \<le> weight (s+J+Suc i)"
        using ascent[OF less] by simp
    qed
    have iter: "weight (s+J) - real (K-J) * (-amin/4) \<le>
        weight (s+J+(K-J))"
      using raw by simp
    have endpoint: "weight (s+K) = weight (s+J+(K-J))"
      using burn(1) by simp
    show False using prefix iter long final endpoint by linarith
  qed
  have negative: "moment (s+K) < 0"
    by (rule anchor_positive_has_negative_moment[OF start anchor positive])
  show ?thesis using positive negative by blast
qed

section \<open>Epoch-independent block regions\<close>

lemma anchor_block_upper_linear:
  assumes start: "weight s \<le> 0"
    and anchor: "\<And>i. i < j \<Longrightarrow> label (s+i)"
  shows "weight (s+j) \<le> real j*S"
  using anchor
proof (induction j)
  case 0
  then show ?case using start by simp
next
  case (Suc j)
  have ih: "weight (s+j) \<le> real j*S"
    by (rule Suc.IH) (use Suc.prems in auto)
  have nonnegative_bound: "0 \<le> real j*S"
    by (rule mult_nonneg_nonneg) (use S_positive in auto)
  have step: "weight (Suc (s+j)) \<le> max (weight (s+j)) 0 + S"
    by (rule weight_step_upper)
  have maximum: "max (weight (s+j)) 0 \<le> real j*S"
    using ih nonnegative_bound by simp
  show ?case using step maximum
    by (simp add: algebra_simps) linarith
qed

lemma tail_block_lower_linear:
  assumes start: "0 \<le> weight s"
    and tail: "\<And>i. i < j \<Longrightarrow> \<not> label (s+i)"
  shows "- real j*S \<le> weight (s+j)"
  using tail
proof (induction j)
  case 0
  then show ?case using start by simp
next
  case (Suc j)
  have ih: "- real j*S \<le> weight (s+j)"
    by (rule Suc.IH) (use Suc.prems in auto)
  have nonpositive_bound: "- real j*S \<le> 0"
    using S_positive by simp
  have step: "min (weight (s+j)) 0 - S \<le> weight (Suc (s+j))"
    by (rule weight_step_lower)
  have minimum: "- real j*S \<le> min (weight (s+j)) 0"
    using ih nonpositive_bound by simp
  show ?case using step minimum
    by (simp add: algebra_simps) linarith
qed

lemma tail_last_step_margin:
  assumes tail: "\<not> label k"
    and lower: "-B \<le> weight k"
    and negative: "weight k < 0"
    and positive_moment: "0 < moment k"
  shows "weight (Suc k) \<le> - amin*(1-beta)*sigmoid (-B)"
proof -
  have sigmoid_lower: "sigmoid (-B) \<le> sigmoid (weight k)"
    using sigmoid_lower_bound[of B "weight k"] lower
    by (simp add: sigmoid_def)
  have old_nonnegative: "0 \<le> beta * moment k"
    by (rule mult_nonneg_nonneg) (use beta_nonnegative positive_moment in auto)
  have new_lower: "(1-beta)*sigmoid (-B) \<le>
      (1-beta)*sigmoid (weight k)"
    by (rule mult_left_mono[OF sigmoid_lower one_minus_beta_nonnegative])
  have rec: "moment (Suc k) = beta*moment k +
      (1-beta)*sigmoid (weight k)"
    using moment_rec[of k] tail by (simp add: bool_value_def)
  have moment_lower: "(1-beta)*sigmoid (-B) \<le> moment (Suc k)"
    using rec old_nonnegative new_lower by linarith
  have floor_positive: "0 < (1-beta)*sigmoid (-B)"
    by (rule mult_pos_pos) (use beta_less_one sigmoid_pos in auto)
  have moment_nonnegative: "0 \<le> moment (Suc k)"
    using moment_lower floor_positive by linarith
  have scaled_step: "amin * moment (Suc k) \<le>
      a (Suc k) * moment (Suc k)"
    by (rule mult_right_mono[OF step_lower moment_nonnegative])
  have scaled_floor: "amin*(1-beta)*sigmoid (-B) \<le>
      amin * moment (Suc k)"
    using mult_left_mono[OF moment_lower, of amin] amin_positive
    by (simp add: algebra_simps)
  have contraction: "rho * weight k \<le> 0"
    by (rule mult_nonneg_nonpos) (use negative rho_nonnegative in auto)
  have weight: "weight (Suc k) = rho*weight k - a (Suc k)*moment (Suc k)"
    by (rule weight_rec)
  show ?thesis using scaled_step scaled_floor contraction weight by linarith
qed

lemma anchor_last_step_margin:
  assumes anchor: "label k"
    and upper: "weight k \<le> B"
    and positive: "0 < weight k"
    and negative_moment: "moment k < 0"
  shows "amin*(1-beta)*sigmoid (-B) \<le> weight (Suc k)"
proof -
  have sigmoid_lower: "sigmoid (-B) \<le> sigmoid (- weight k)"
    proof -
    have order: "-B \<le> - weight k" using upper by linarith
    show ?thesis using sigmoid_lower_bound[OF order]
      by (simp add: sigmoid_def)
  qed
  have old_nonpositive: "beta * moment k \<le> 0"
    by (rule mult_nonneg_nonpos) (use beta_nonnegative negative_moment in auto)
  have new_upper: "(1-beta) * (- sigmoid (- weight k)) \<le>
      - ((1-beta)*sigmoid (-B))"
    using mult_left_mono[OF sigmoid_lower one_minus_beta_nonnegative]
    by linarith
  have rec: "moment (Suc k) = beta*moment k -
      (1-beta)*sigmoid (- weight k)"
    using moment_rec[of k] anchor
    by (simp add: bool_value_def sigmoid_neg_identity algebra_simps)
  have moment_upper: "moment (Suc k) \<le> - ((1-beta)*sigmoid (-B))"
    using rec old_nonpositive new_upper by linarith
  have floor_positive: "0 < (1-beta)*sigmoid (-B)"
    by (rule mult_pos_pos) (use beta_less_one sigmoid_pos in auto)
  have neg_moment_nonnegative: "0 \<le> - moment (Suc k)"
    using moment_upper floor_positive by linarith
  have scaled_step: "amin * (- moment (Suc k)) \<le>
      a (Suc k) * (- moment (Suc k))"
    by (rule mult_right_mono[OF step_lower neg_moment_nonnegative])
  have scaled_floor: "amin*(1-beta)*sigmoid (-B) \<le>
      amin * (- moment (Suc k))"
    using mult_left_mono[of "(1-beta)*sigmoid (-B)"
      "- moment (Suc k)" amin] moment_upper amin_positive
    by (simp add: algebra_simps)
  have contraction: "0 \<le> rho * weight k"
    by (rule mult_nonneg_nonneg) (use positive rho_nonnegative in auto)
  have weight: "weight (Suc k) = rho*weight k - a (Suc k)*moment (Suc k)"
    by (rule weight_rec)
  show ?thesis using scaled_step scaled_floor contraction weight by linarith
qed
lemma anchor_then_tail_region:
  assumes negative_start: "- real m*S \<le> weight s" "weight s \<le> 0"
    and anchor: "\<And>i. i < n \<Longrightarrow> label (s+i)"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> label (s+n+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
  shows "- real m*S \<le> weight (s+n+m) \<and>
    weight (s+n+m) < 0 \<and> 0 < moment (s+n+m) \<and>
    weight (s+n+m) \<le> - amin*(1-beta)*sigmoid (- real m*S)"
proof -
  have J_anchor: "J \<le> n-1" using sizes(1) by linarith
  have anchor_prefix_labels: "\<And>i. i < n-1 \<Longrightarrow> label (s+i)"
    by (rule anchor) linarith
  have anchor_cross: "0 < weight (s+(n-1)) \<and> moment (s+(n-1)) < 0"
  proof (rule anchor_block_crossing[where B="real m*S" and K="n-1" and J=J])
    show "weight s \<le> 0" by (rule negative_start(2))
    show "- (real m*S) \<le> weight s" using negative_start(1) by simp
    show "\<And>i. i < n-1 \<Longrightarrow> label (s+i)" by (rule anchor_prefix_labels)
    show "J \<le> n-1" by (rule J_anchor)
    show "beta^J \<le> 1/6" by (rule burn)
    show "real m*S + real J*S < real (n-1-J) * (amin/4)"
      by (rule anchor_long)
  qed
  have anchor_cross_weight: "0 < weight (s+(n-1))" using anchor_cross by blast
  have anchor_cross_moment: "moment (s+(n-1)) < 0" using anchor_cross by blast
  have last_anchor_label: "label (s+(n-1))"
    by (rule anchor) (use sizes(1) in linarith)
  have anchor_end_raw: "0 < weight (Suc (s+(n-1))) \<and>
      moment (Suc (s+(n-1))) < 0"
    by (rule anchor_positive_step[OF last_anchor_label anchor_cross_weight
          anchor_cross_moment])
  have anchor_end_weight: "0 < weight (s+n)"
    using anchor_end_raw sizes(1) by simp
  have anchor_end_moment: "moment (s+n) < 0"
    using anchor_end_raw sizes(1) by simp
  have anchor_upper: "weight (s+n) \<le> real n*S"
    by (rule anchor_block_upper_linear[OF negative_start(2) anchor])
  have J_tail: "J \<le> m-1" using sizes(2) by linarith
  have tail_prefix_labels: "\<And>i. i < m-1 \<Longrightarrow> \<not> label ((s+n)+i)"
    using tail by (simp add: add.assoc)
  have tail_cross: "weight ((s+n)+(m-1)) < 0 \<and>
      0 < moment ((s+n)+(m-1))"
  proof (rule tail_block_crossing[where B="real n*S" and K="m-1" and J=J])
    show "0 \<le> weight (s+n)" using anchor_end_weight by linarith
    show "weight (s+n) \<le> real n*S" by (rule anchor_upper)
    show "\<And>i. i < m-1 \<Longrightarrow> \<not> label ((s+n)+i)" by (rule tail_prefix_labels)
    show "J \<le> m-1" by (rule J_tail)
    show "beta^J \<le> 1/6" by (rule burn)
    show "real n*S + real J*S < real (m-1-J) * (amin/4)"
      by (rule tail_long)
  qed
  have tail_cross_weight: "weight ((s+n)+(m-1)) < 0" using tail_cross by blast
  have tail_cross_moment: "0 < moment ((s+n)+(m-1))" using tail_cross by blast
have last_tail_label: "\<not> label ((s+n)+(m-1))"
    using tail[of "m-1"] sizes(2) by (simp add: add.assoc)
  have tail_end_raw: "weight (Suc ((s+n)+(m-1))) < 0 \<and>
      0 < moment (Suc ((s+n)+(m-1)))"
    by (rule tail_negative_step[OF last_tail_label tail_cross_weight tail_cross_moment])
  have tail_end: "weight (s+n+m) < 0 \<and> 0 < moment (s+n+m)"
    using tail_end_raw sizes(2) by (simp add: add.assoc)
  have tail_labels: "\<And>i. i < m \<Longrightarrow> \<not> label ((s+n)+i)"
    using tail by (simp add: add.assoc)
  have tail_lower: "- real m*S \<le> weight ((s+n)+m)"
    by (rule tail_block_lower_linear[OF _ tail_labels])
      (use anchor_end_weight in linarith)
  have prior_lower_raw: "- real (m-1)*S \<le> weight ((s+n)+(m-1))"
    by (rule tail_block_lower_linear[OF _ tail_prefix_labels])
      (use anchor_end_weight in linarith)
  have count_bound: "real (m-1)*S \<le> real m*S"
    by (rule mult_right_mono) (use S_positive in auto)
  have prior_lower: "- real m*S \<le> weight ((s+n)+(m-1))"
    using prior_lower_raw count_bound by linarith
have margin_raw: "weight (Suc ((s+n)+(m-1))) \<le>
      - amin*(1-beta)*sigmoid (-(real m*S))"
  proof (rule tail_last_step_margin[where B="real m*S" and
        k="(s+n)+(m-1)"])
    show "\<not> label ((s+n)+(m-1))" by (rule last_tail_label)
    show "- (real m*S) \<le> weight ((s+n)+(m-1))"
      using prior_lower by simp
    show "weight ((s+n)+(m-1)) < 0" by (rule tail_cross_weight)
    show "0 < moment ((s+n)+(m-1))" by (rule tail_cross_moment)
  qed  have margin: "weight (s+n+m) \<le>
      - amin*(1-beta)*sigmoid (- real m*S)"
    using margin_raw sizes(2) by (simp add: add.assoc)
  show ?thesis using tail_end tail_lower margin by (simp add: add.assoc)
qed

lemma tail_then_anchor_region:
  assumes positive_start: "0 \<le> weight s" "weight s \<le> real n*S"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> label (s+i)"
    and anchor: "\<And>i. i < n \<Longrightarrow> label (s+m+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
  shows "0 < weight (s+m+n) \<and> weight (s+m+n) \<le> real n*S \<and>
    moment (s+m+n) < 0 \<and>
    amin*(1-beta)*sigmoid (- real n*S) \<le> weight (s+m+n)"
proof -
  have J_tail: "J \<le> m-1" using sizes(2) by linarith
  have tail_prefix_labels: "\<And>i. i < m-1 \<Longrightarrow> \<not> label (s+i)"
    by (rule tail) linarith
  have tail_cross: "weight (s+(m-1)) < 0 \<and> 0 < moment (s+(m-1))"
  proof (rule tail_block_crossing[where B="real n*S" and K="m-1" and J=J])
    show "0 \<le> weight s" by (rule positive_start(1))
    show "weight s \<le> real n*S" by (rule positive_start(2))
    show "\<And>i. i < m-1 \<Longrightarrow> \<not> label (s+i)" by (rule tail_prefix_labels)
    show "J \<le> m-1" by (rule J_tail)
    show "beta^J \<le> 1/6" by (rule burn)
    show "real n*S + real J*S < real (m-1-J) * (amin/4)"
      by (rule tail_long)
  qed
  have tail_cross_weight: "weight (s+(m-1)) < 0" using tail_cross by blast
  have tail_cross_moment: "0 < moment (s+(m-1))" using tail_cross by blast
  have last_tail_label: "\<not> label (s+(m-1))"
    using tail[of "m-1"] sizes(2) by simp
  have tail_end_raw: "weight (Suc (s+(m-1))) < 0 \<and>
      0 < moment (Suc (s+(m-1)))"
    by (rule tail_negative_step[OF last_tail_label tail_cross_weight tail_cross_moment])
  have tail_end_weight: "weight (s+m) < 0"
    using tail_end_raw sizes(2) by simp
  have tail_end_moment: "0 < moment (s+m)"
    using tail_end_raw sizes(2) by simp
  have tail_lower: "- real m*S \<le> weight (s+m)"
    by (rule tail_block_lower_linear[OF positive_start(1) tail])
  have J_anchor: "J \<le> n-1" using sizes(1) by linarith
  have anchor_prefix_labels: "\<And>i. i < n-1 \<Longrightarrow> label ((s+m)+i)"
    using anchor by (simp add: add.assoc)
  have anchor_cross: "0 < weight ((s+m)+(n-1)) \<and>
      moment ((s+m)+(n-1)) < 0"
  proof (rule anchor_block_crossing[where B="real m*S" and K="n-1" and J=J])
    show "weight (s+m) \<le> 0" using tail_end_weight by linarith
    show "- (real m*S) \<le> weight (s+m)" using tail_lower by simp
    show "\<And>i. i < n-1 \<Longrightarrow> label ((s+m)+i)" by (rule anchor_prefix_labels)
    show "J \<le> n-1" by (rule J_anchor)
    show "beta^J \<le> 1/6" by (rule burn)
    show "real m*S + real J*S < real (n-1-J) * (amin/4)"
      by (rule anchor_long)
  qed
  have anchor_cross_weight: "0 < weight ((s+m)+(n-1))" using anchor_cross by blast
  have anchor_cross_moment: "moment ((s+m)+(n-1)) < 0" using anchor_cross by blast
  have last_anchor_label: "label ((s+m)+(n-1))"
    using anchor[of "n-1"] sizes(1) by (simp add: add.assoc)
  have anchor_end_raw: "0 < weight (Suc ((s+m)+(n-1))) \<and>
      moment (Suc ((s+m)+(n-1))) < 0"
    by (rule anchor_positive_step[OF last_anchor_label anchor_cross_weight
          anchor_cross_moment])
  have anchor_end: "0 < weight (s+m+n) \<and> moment (s+m+n) < 0"
    using anchor_end_raw sizes(1) by (simp add: add.assoc)
  have anchor_labels: "\<And>i. i < n \<Longrightarrow> label ((s+m)+i)"
    using anchor by (simp add: add.assoc)
  have anchor_upper: "weight ((s+m)+n) \<le> real n*S"
    by (rule anchor_block_upper_linear[OF _ anchor_labels])
      (use tail_end_weight in linarith)
  have prior_upper_raw: "weight ((s+m)+(n-1)) \<le> real (n-1)*S"
    by (rule anchor_block_upper_linear[OF _ anchor_prefix_labels])
      (use tail_end_weight in linarith)
  have count_bound: "real (n-1)*S \<le> real n*S"
    by (rule mult_right_mono) (use S_positive in auto)
  have prior_upper: "weight ((s+m)+(n-1)) \<le> real n*S"
    using prior_upper_raw count_bound by linarith
  have margin_raw: "amin*(1-beta)*sigmoid (-(real n*S)) \<le>
      weight (Suc ((s+m)+(n-1)))"
  proof (rule anchor_last_step_margin[where B="real n*S" and
        k="(s+m)+(n-1)"])
    show "label ((s+m)+(n-1))" by (rule last_anchor_label)
    show "weight ((s+m)+(n-1)) \<le> real n*S" by (rule prior_upper)
    show "0 < weight ((s+m)+(n-1))" by (rule anchor_cross_weight)
    show "moment ((s+m)+(n-1)) < 0" by (rule anchor_cross_moment)
  qed
  have margin: "amin*(1-beta)*sigmoid (- real n*S) \<le> weight (s+m+n)"
    using margin_raw sizes(1) by (simp add: add.assoc)
  show ?thesis using anchor_end anchor_upper margin by (simp add: add.assoc)
qed

section \<open>All epoch boundaries without state resets\<close>

lemma anchor_tail_all_epochs_region:
  assumes anchor_schedule: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+i)"
    and tail_schedule: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+n+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
  shows "- real m*S \<le> weight (E*(n+m)) \<and> weight (E*(n+m)) \<le> 0 \<and>
    (E=0 \<or> (weight (E*(n+m)) < 0 \<and> 0 < moment (E*(n+m)) \<and>
      weight (E*(n+m)) \<le> - amin*(1-beta)*sigmoid (- real m*S)))"
proof (induction E)
  case 0
  have "- real m*S \<le> 0" using S_positive by simp
  then show ?case by simp
next
  case (Suc E)
  have start_lower: "- real m*S \<le> weight (E*(n+m))" using Suc.IH by blast
  have start_upper: "weight (E*(n+m)) \<le> 0" using Suc.IH by blast
  have anchors: "\<And>i. i < n \<Longrightarrow> label (E*(n+m)+i)"
    by (rule anchor_schedule)
  have tails: "\<And>i. i < m \<Longrightarrow> \<not> label (E*(n+m)+n+i)"
    by (rule tail_schedule)
have transition_full: "- real m*S \<le> weight (E*(n+m)+n+m) \<and>
      weight (E*(n+m)+n+m) < 0 \<and> 0 < moment (E*(n+m)+n+m) \<and>
      weight (E*(n+m)+n+m) \<le>
        - amin*(1-beta)*sigmoid (- real m*S)"
    by (rule anchor_then_tail_region[OF start_lower start_upper anchors tails
          sizes burn anchor_long tail_long])
  have transition: "- real m*S \<le> weight (E*(n+m)+n+m) \<and>
      weight (E*(n+m)+n+m) < 0 \<and> 0 < moment (E*(n+m)+n+m)"
    using transition_full by blast
  show ?case using transition_full by (simp add: algebra_simps)
qed

lemma anchor_tail_all_epochs_negative:
  assumes schedule_anchor: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+i)"
    and schedule_tail: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+n+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
    and epoch: "1 \<le> E"
  shows "weight (E*(n+m)) < 0 \<and> 0 < moment (E*(n+m))"
  using anchor_tail_all_epochs_region[OF schedule_anchor schedule_tail sizes burn
        anchor_long tail_long, of E] epoch by auto

lemma anchor_tail_all_epochs_margin:
  assumes schedule_anchor: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+i)"
    and schedule_tail: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+n+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
    and epoch: "1 \<le> E"
  shows "weight (E*(n+m)) \<le>
    - amin*(1-beta)*sigmoid (- real m*S)"
  using anchor_tail_all_epochs_region[OF schedule_anchor schedule_tail sizes burn
        anchor_long tail_long, of E] epoch by auto

lemma tail_anchor_all_epochs_region:
  assumes tail_schedule: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+i)"
    and anchor_schedule: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+m+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
  shows "0 \<le> weight (E*(n+m)) \<and> weight (E*(n+m)) \<le> real n*S \<and>
    (E=0 \<or> (0 < weight (E*(n+m)) \<and> moment (E*(n+m)) < 0 \<and>
      amin*(1-beta)*sigmoid (- real n*S) \<le> weight (E*(n+m))))"
proof (induction E)
  case 0
  have "0 \<le> real n*S" using S_positive by simp
  then show ?case by simp
next
  case (Suc E)
  have start_lower: "0 \<le> weight (E*(n+m))" using Suc.IH by blast
  have start_upper: "weight (E*(n+m)) \<le> real n*S" using Suc.IH by blast
  have tails: "\<And>i. i < m \<Longrightarrow> \<not> label (E*(n+m)+i)"
    by (rule tail_schedule)
  have anchors: "\<And>i. i < n \<Longrightarrow> label (E*(n+m)+m+i)"
    by (rule anchor_schedule)
  have transition_full: "0 < weight (E*(n+m)+m+n) \<and>
      weight (E*(n+m)+m+n) \<le> real n*S \<and>
      moment (E*(n+m)+m+n) < 0 \<and>
      amin*(1-beta)*sigmoid (- real n*S) \<le> weight (E*(n+m)+m+n)"
    by (rule tail_then_anchor_region[OF start_lower start_upper tails anchors
          sizes burn anchor_long tail_long])
  show ?case using transition_full by (simp add: algebra_simps)
qed

lemma tail_anchor_all_epochs_positive:
  assumes schedule_tail: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+i)"
    and schedule_anchor: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+m+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
    and epoch: "1 \<le> E"
  shows "0 < weight (E*(n+m)) \<and> moment (E*(n+m)) < 0"
  using tail_anchor_all_epochs_region[OF schedule_tail schedule_anchor sizes burn
        anchor_long tail_long, of E] epoch by auto

lemma tail_anchor_all_epochs_margin:
  assumes schedule_tail: "\<And>e i. i < m \<Longrightarrow> \<not> label (e*(n+m)+i)"
    and schedule_anchor: "\<And>e i. i < n \<Longrightarrow> label (e*(n+m)+m+i)"
    and sizes: "J+2 \<le> n" "J+2 \<le> m"
    and burn: "beta^J \<le> 1/6"
    and anchor_long: "real m*S + real J*S <
      real ((n-1)-J) * (amin/4)"
    and tail_long: "real n*S + real J*S <
      real ((m-1)-J) * (amin/4)"
    and epoch: "1 \<le> E"
  shows "amin*(1-beta)*sigmoid (- real n*S) \<le> weight (E*(n+m))"
  using tail_anchor_all_epochs_region[OF schedule_tail schedule_anchor sizes burn
        anchor_long tail_long, of E] epoch by auto

end
end


