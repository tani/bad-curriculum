theory Adam_Bridge
  imports Adam_Core
begin

section \<open>Bridging lemmas for the exact Adam/AdamW core\<close>

text \<open>
  Two connections are established here. First, an explicit logarithmic upper
  bound for the Anchor endpoint, which discharges the anchor_bound premise of
  the finite inversion theorems. Second, a deterministic interval-drift
  certificate derived from a prefix-discrepancy hypothesis, which discharges
  the interval premise of the barrier theorem.
\<close>

lemma aw_ema_cong:
  assumes "\<And>i. i < n \<Longrightarrow> x i = y i"
  shows "aw_ema beta x n = aw_ema beta y n"
  using assms by (induction n) simp_all

lemma aw_ema_diff:
  "aw_ema beta (\<lambda>i. x i - y i) n =
    aw_ema beta x n - aw_ema beta y n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have expand: "aw_ema beta (\<lambda>i. x i - y i) (Suc n) =
      beta * (aw_ema beta x n - aw_ema beta y n) + (1-beta) * (x n - y n)"
    using Suc.IH by simp
  have regroup: "beta * (aw_ema beta x n - aw_ema beta y n) +
      (1-beta) * (x n - y n) =
      (beta * aw_ema beta x n + (1-beta) * x n) -
      (beta * aw_ema beta y n + (1-beta) * y n)"
    by (simp add: algebra_simps)
  show ?case using expand regroup by simp
qed

lemma aw_ema_nonneg:
  assumes beta: "0 \<le> beta" "beta \<le> 1"
    and x: "\<And>i. i < n \<Longrightarrow> 0 \<le> x i"
  shows "0 \<le> aw_ema beta x n"
proof -
  have "aw_ema beta (\<lambda>i. 0) n \<le> aw_ema beta x n"
    by (rule aw_ema_mono[OF beta]) (use x in auto)
  then show ?thesis by (simp add: aw_ema_constant)
qed

lemma aw_ema_le_one:
  assumes beta: "0 \<le> beta" "beta \<le> 1"
    and x: "\<And>i. i < n \<Longrightarrow> x i \<le> 1"
  shows "aw_ema beta x n \<le> 1 - beta^n"
proof -
  have "aw_ema beta x n \<le> aw_ema beta (\<lambda>i. 1) n"
    by (rule aw_ema_mono[OF beta]) (use x in auto)
  then show ?thesis by (simp add: aw_ema_constant)
qed

section \<open>Deterministic tracking of the corrected first moment\<close>

context aw_parameters
begin

abbreviation alpha where "alpha \<equiv> eta/eps"
abbreviation Kslack where "Kslack \<equiv> beta1 * eta / (2 * eps * (1-beta1))"
abbreviation Sema where
  "Sema b k \<equiv> aw_ema beta1 (\<lambda>i. sigmoid (W b i)) k"
abbreviation Bema where
  "Bema b k \<equiv> aw_ema beta1 (\<lambda>i. bool_value (b i)) k"
abbreviation ZH where "ZH b k \<equiv> Bema b k / (1-beta1^k)"

lemma aw_slack_nonneg: "0 \<le> Kslack"
  using beta1_nonneg beta1_lt eta_pos eps_pos by simp

lemma aw_slack_identity: "beta1 * (Kslack + eta/(2*eps)) = Kslack"
proof -
  have ne: "1 - beta1 \<noteq> 0" using beta1_lt by simp
  have ne2: "eps \<noteq> 0" using eps_pos by simp
  show ?thesis using ne ne2 by (simp add: field_simps)
qed

lemma aw_sigma_shift:
  "abs (sigmoid (W b k) - sigmoid (W b (Suc k))) \<le> eta/(2*eps)"
proof -
  have lip: "abs (sigmoid (W b k) - sigmoid (W b (Suc k))) \<le>
      abs (W b k - W b (Suc k)) / 4"
    by (rule sigmoid_lipschitz)
  have jump: "abs (W b k - W b (Suc k)) \<le> 2*eta/eps"
    using aw_jump_bound[of b k] by (simp add: abs_minus_commute)
  have scaled: "abs (W b k - W b (Suc k)) / 4 \<le> (2*eta/eps) / 4"
    using jump by simp
  have simplify: "(2*eta/eps) / 4 = eta/(2*eps)"
    using eps_pos by simp
  show ?thesis using lip scaled simplify by argo
qed

lemma aw_sigma_ema_track:
  "abs (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) \<le>
    (1-beta1^(Suc k)) * Kslack"
proof (induction k)
  case 0
  have base: "Sema b (Suc 0) = (1-beta1) * sigmoid (W b 0)"
    by simp
  have nonneg: "0 \<le> (1-beta1) * Kslack"
    by (rule mult_nonneg_nonneg) (use beta1_lt aw_slack_nonneg in auto)
  show ?case using nonneg by (simp add: base)
next
  case (Suc k)
  let ?t = "1-beta1^(Suc k)"
  let ?s = "sigmoid (W b k)"
  let ?s' = "sigmoid (W b (Suc k))"
  have tpos: "0 \<le> ?t"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by simp
  have expand: "Sema b (Suc (Suc k)) = beta1 * Sema b (Suc k) + (1-beta1) * ?s'"
    by simp
  have corr: "1 - beta1^(Suc (Suc k)) = beta1 * ?t + (1-beta1)"
    by (simp add: algebra_simps)
  have diff: "Sema b (Suc (Suc k)) - (1 - beta1^(Suc (Suc k))) * ?s' =
      beta1 * ((Sema b (Suc k) - ?t * ?s) + ?t * (?s - ?s'))"
    using expand corr by (simp add: algebra_simps)
  have shift: "abs (?s - ?s') \<le> eta/(2*eps)"
    by (rule aw_sigma_shift)
  have inner: "abs ((Sema b (Suc k) - ?t * ?s) + ?t * (?s - ?s')) \<le>
      ?t * Kslack + ?t * (eta/(2*eps))"
  proof -
    have a: "abs (Sema b (Suc k) - ?t * ?s) \<le> ?t * Kslack"
      by (rule Suc.IH)
    have b: "abs (?t * (?s - ?s')) \<le> ?t * (eta/(2*eps))"
    proof -
      have factor: "abs (?t * (?s - ?s')) = ?t * abs (?s - ?s')"
        using tpos by (simp add: abs_mult)
      have bounded: "?t * abs (?s - ?s') \<le> ?t * (eta/(2*eps))"
        by (rule mult_left_mono[OF shift tpos])
      show ?thesis using factor bounded by linarith
    qed
    show ?thesis using a b by linarith
  qed
  have scaled: "abs (Sema b (Suc (Suc k)) - (1 - beta1^(Suc (Suc k))) * ?s') \<le>
      beta1 * (?t * Kslack + ?t * (eta/(2*eps)))"
    using diff inner beta1_nonneg by (simp add: abs_mult mult_left_mono)
  have collapse: "beta1 * (?t * Kslack + ?t * (eta/(2*eps))) = ?t * Kslack"
  proof -
    have regroup: "beta1 * (?t * Kslack + ?t * (eta/(2*eps))) =
        ?t * (beta1 * (Kslack + eta/(2*eps)))"
      by (simp add: algebra_simps)
    show ?thesis using regroup aw_slack_identity by simp
  qed
  have monotone: "?t * Kslack \<le> (1 - beta1^(Suc (Suc k))) * Kslack"
  proof -
    have power: "beta1^(Suc (Suc k)) \<le> beta1^(Suc k)"
      by (rule aw_power_antimono) (use beta1_nonneg beta1_lt in auto)
    have le: "1 - beta1^(Suc k) \<le> 1 - beta1^(Suc (Suc k))"
      using power by simp
    show ?thesis by (rule mult_right_mono[OF le aw_slack_nonneg])
  qed
  show ?case using scaled collapse monotone by linarith
qed

lemma aw_bias_positive: "0 < 1 - beta1^(Suc k)"
  using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by simp

lemma aw_bema_bounds:
  "0 \<le> Bema b k" "Bema b k \<le> 1 - beta1^k"
proof -
  show "0 \<le> Bema b k"
    by (rule aw_ema_nonneg) (use beta1_nonneg beta1_lt bool_value_def in auto)
  show "Bema b k \<le> 1 - beta1^k"
    by (rule aw_ema_le_one) (use beta1_nonneg beta1_lt bool_value_def in auto)
qed

lemma aw_zh_bounds:
  "0 \<le> ZH b (Suc k)" "ZH b (Suc k) \<le> 1"
proof -
  have pos: "0 < 1 - beta1^(Suc k)" by (rule aw_bias_positive)
  show "0 \<le> ZH b (Suc k)"
    using aw_bema_bounds(1)[of b "Suc k"] pos by simp
  show "ZH b (Suc k) \<le> 1"
    using aw_bema_bounds(2)[of b "Suc k"] pos by (simp add: divide_le_eq)
qed

lemma aw_moment_split:
  "M b k = Sema b k - Bema b k"
proof -
  have ema: "M b k = aw_ema beta1 (G b) k" by (rule aw_m_ema)
  have split: "aw_ema beta1 (\<lambda>i. sigmoid (W b i) - bool_value (b i)) k =
      Sema b k - Bema b k"
    by (rule aw_ema_diff)
  show ?thesis using ema split by simp
qed

lemma aw_moment_track:
  "abs (MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k))) \<le> Kslack"
proof -
  have pos: "0 < 1 - beta1^(Suc k)" by (rule aw_bias_positive)
  have tne: "1 - beta1^(Suc k) \<noteq> 0" using pos by simp
  have split: "M b (Suc k) = Sema b (Suc k) - Bema b (Suc k)"
    by (rule aw_moment_split)
  have combine: "MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k)) =
      Sema b (Suc k) / (1-beta1^(Suc k)) - sigmoid (W b k)"
    using split by (simp add: diff_divide_distrib)
  have quotient: "Sema b (Suc k) / (1-beta1^(Suc k)) - sigmoid (W b k) =
      (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k))"
    using tne by (simp add: field_simps)
  have track: "abs (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) \<le>
      (1-beta1^(Suc k)) * Kslack"
    by (rule aw_sigma_ema_track)
  have divided:
      "abs (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k)) \<le>
      ((1-beta1^(Suc k)) * Kslack) / (1-beta1^(Suc k))"
    by (rule divide_right_mono[OF track]) (use pos in simp)
  have cancel: "((1-beta1^(Suc k)) * Kslack) / (1-beta1^(Suc k)) = Kslack"
    using tne by simp
  have eq: "MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k)) =
      (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k))"
    by (rule trans[OF combine quotient])
  have absval: "abs (MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k))) =
      abs ((Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k)))"
    by (rule arg_cong[where f = abs, OF eq])
  have absform: "abs ((Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k))) =
      abs (Sema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (W b k)) /
        (1-beta1^(Suc k))"
    using pos by simp
  show ?thesis using absval absform divided cancel by linarith
qed

end

section \<open>Explicit logarithmic Anchor bound\<close>

lemma anchor_step_mono:
  assumes a: "0 \<le> a" "a \<le> 4" and xy: "x \<le> y"
  shows "anchor_step a x \<le> anchor_step a y"
proof -
  have absxy: "abs (-y - -x) = y - x" using xy by simp
  have lip: "abs (sigmoid (-y) - sigmoid (-x)) \<le> abs (-y - -x) / 4"
    by (rule sigmoid_lipschitz)
  have gap: "sigmoid (-x) - sigmoid (-y) \<le> (y-x) / 4"
  proof -
    have self: "sigmoid (-x) - sigmoid (-y) \<le>
        abs (sigmoid (-x) - sigmoid (-y))"
      by (rule abs_ge_self)
    have commute: "abs (sigmoid (-x) - sigmoid (-y)) =
        abs (sigmoid (-y) - sigmoid (-x))"
      by (rule abs_minus_commute)
    show ?thesis using self commute lip absxy by argo
  qed
  have scaled: "a * (sigmoid (-x) - sigmoid (-y)) \<le> a * ((y-x)/4)"
    by (rule mult_left_mono[OF gap a(1)])
  have small: "a * ((y-x)/4) \<le> y - x"
  proof -
    have quarter: "a/4 \<le> 1" using a(2) by simp
    have nonneg: "0 \<le> y - x" using xy by simp
    have factor: "a * ((y-x)/4) = (a/4) * (y-x)" by simp
    have bounded: "(a/4) * (y-x) \<le> 1 * (y-x)"
      by (rule mult_right_mono[OF quarter nonneg])
    show ?thesis using factor bounded by simp
  qed
  have combined: "a * (sigmoid (-x) - sigmoid (-y)) \<le> y - x"
    using scaled small by linarith
  have key: "a * sigmoid (-x) - a * sigmoid (-y) \<le> y - x"
    using combined by (simp add: algebra_simps)
  show ?thesis unfolding anchor_step_def using key by linarith
qed

lemma anchor_step_shift:
  assumes a: "0 \<le> a" and t: "0 \<le> t"
  shows "anchor_step a (x + t) \<le> anchor_step a x + t"
proof -
  have mono: "sigmoid (-(x+t)) \<le> sigmoid (-x)"
    using sigmoid_difference_bounds(1)[of "-(x+t)" "-x"] t by simp
  have scaled: "a * sigmoid (-(x+t)) \<le> a * sigmoid (-x)"
    by (rule mult_left_mono[OF mono a])
  show ?thesis using scaled by (simp add: anchor_step_def algebra_simps)
qed

lemma anchor_state_Suc:
  "anchor_state a (Suc n) = anchor_step a (anchor_state a n)"
  by (simp add: anchor_state_def funpow_Suc_right)

lemma real_scaled_telescope:
  fixes c d x y z :: real
  shows "c * (x - y) / d + c * (y - z) / d = c * (x - z) / d"
proof -
  have combine: "c * (x - y) / d + c * (y - z) / d =
      (c * (x - y) + c * (y - z)) / d"
    by (simp add: add_divide_distrib)
  have collapse: "c * (x - y) + c * (y - z) = c * (x - z)"
    by (simp add: algebra_simps)
  show ?thesis using combine collapse by simp
qed

lemma real_scaled_split:
  fixes e a b c d :: real
  shows "e * (a - b - c) / d = e*a/d - e*b/d - e*c/d"
proof -
  have numerator: "e * (a - b - c) = e*a - e*b - e*c"
    by (simp add: algebra_simps)
  have distribute: "(e*a - e*b - e*c)/d = e*a/d - e*b/d - e*c/d"
    by (simp add: diff_divide_distrib)
  show ?thesis using numerator distribute by simp
qed

context aw_parameters
begin

lemma aw_anchor_weight_step:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and kn: "k < n"
  shows "W b (Suc k) \<le> anchor_step alpha (W b k) + alpha * Kslack"
proof -
  have wk: "0 \<le> W b k"
  proof -
    have pair: "0 \<le> W b k \<and> M b k \<le> 0"
      by (rule aw_anchor_prefix) (use anchor kn in auto)
    show ?thesis using pair by simp
  qed
  have dp: "0 < D b (Suc k)" by (rule aw_den_positive)
  have dlow: "eps \<le> D b (Suc k)" by (rule aw_den_bounds(1))
  have zh: "ZH b (Suc k) = 1"
  proof -
    have bema: "Bema b (Suc k) = aw_ema beta1 (\<lambda>i. 1) (Suc k)"
      by (rule aw_ema_cong) (use anchor kn bool_value_def in auto)
    have const_ema: "aw_ema beta1 (\<lambda>i. (1::real)) (Suc k) = 1 - beta1^(Suc k)"
      by (simp add: aw_ema_constant)
    have total: "Bema b (Suc k) = 1 - beta1^(Suc k)"
      by (rule trans[OF bema const_ema])
    have ratio: "(1 - beta1^(Suc k)) / (1 - beta1^(Suc k)) = 1"
      using aw_bias_positive[of k] by simp
    show ?thesis unfolding total by (rule ratio)
  qed
  have lower: "- sigmoid (- W b k) - Kslack \<le> MH b (Suc k)"
  proof -
    have track: "abs (MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k))) \<le>
        Kslack"
      by (rule aw_moment_track)
    have neg: "sigmoid (W b k) - 1 = - sigmoid (- W b k)"
      by (simp add: sigmoid_neg_identity)
    show ?thesis using track zh neg by (simp add: abs_le_iff)
  qed
  have num_nonneg: "0 \<le> sigmoid (- W b k) + Kslack"
    using sigmoid_pos[of "- W b k"] aw_slack_nonneg by linarith
  have scaled0: "eta * (- sigmoid (- W b k) - Kslack) \<le> eta * MH b (Suc k)"
    by (rule mult_left_mono[OF lower]) (use eta_pos in simp)
  have dist: "eta * (- sigmoid (- W b k) - Kslack) =
      - (eta * (sigmoid (- W b k) + Kslack))"
    by (simp add: algebra_simps)
  have scaled: "- (eta * MH b (Suc k)) \<le> eta * (sigmoid (- W b k) + Kslack)"
    using scaled0 dist by linarith
  have step1: "(- (eta * MH b (Suc k))) / D b (Suc k) \<le>
      (eta * (sigmoid (- W b k) + Kslack)) / D b (Suc k)"
    by (rule divide_right_mono[OF scaled]) (use dp in simp)
  have step2: "(eta * (sigmoid (- W b k) + Kslack)) / D b (Suc k) \<le>
      (eta * (sigmoid (- W b k) + Kslack)) / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * (sigmoid (- W b k) + Kslack)"
      using num_nonneg eta_pos by simp
    show "0 < D b (Suc k) * eps" using dp eps_pos by simp
  qed
  have quotient: "(- (eta * MH b (Suc k))) / D b (Suc k) \<le>
      (eta * (sigmoid (- W b k) + Kslack)) / eps"
    using step1 step2 by linarith
  have neg_div: "(- (eta * MH b (Suc k))) / D b (Suc k) =
      - (eta * MH b (Suc k) / D b (Suc k))"
    by simp
  have decayed: "(1 - eta*decay) * W b k \<le> W b k"
  proof (rule mult_left_le_one_le[OF wk])
    show "0 \<le> 1 - eta*decay" using decay_step by simp
    show "1 - eta*decay \<le> 1" using eta_pos decay_nonneg by simp
  qed
  have rec: "W b (Suc k) = (1 - eta*decay) * W b k -
      eta * MH b (Suc k) / D b (Suc k)"
    by (rule aw_w_rec)
  have combine: "W b (Suc k) \<le> W b k +
      (eta * (sigmoid (- W b k) + Kslack)) / eps"
    using rec decayed quotient neg_div by linarith
  have expand: "(eta * (sigmoid (- W b k) + Kslack)) / eps =
      alpha * sigmoid (- W b k) + alpha * Kslack"
    by (simp add: algebra_simps add_divide_distrib)
  show ?thesis unfolding anchor_step_def using combine expand by linarith
qed

lemma aw_anchor_weight_le:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and alpha_le: "alpha \<le> 4"
    and jn: "j \<le> n"
  shows "W b j \<le> anchor_state alpha j + real j * (alpha * Kslack)"
  using jn
proof (induction j)
  case 0
  show ?case by (simp add: anchor_state_def aw_zero_def)
next
  case (Suc j)
  have alpha_nonneg: "0 \<le> alpha" using eta_pos eps_pos by simp
  have product: "0 \<le> alpha * Kslack"
    by (rule mult_nonneg_nonneg[OF alpha_nonneg aw_slack_nonneg])
  have slack_nonneg: "0 \<le> real j * (alpha * Kslack)"
    by (rule mult_nonneg_nonneg) (use product in auto)
  have ih: "W b j \<le> anchor_state alpha j + real j * (alpha * Kslack)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have jn: "j < n" using Suc.prems by arith
  have step: "W b (Suc j) \<le> anchor_step alpha (W b j) + alpha * Kslack"
    by (rule aw_anchor_weight_step[OF anchor jn])
  have mono: "anchor_step alpha (W b j) \<le>
      anchor_step alpha (anchor_state alpha j + real j * (alpha * Kslack))"
    by (rule anchor_step_mono[OF alpha_nonneg alpha_le ih])
  have shift: "anchor_step alpha (anchor_state alpha j +
        real j * (alpha * Kslack)) \<le>
      anchor_step alpha (anchor_state alpha j) + real j * (alpha * Kslack)"
    by (rule anchor_step_shift[OF alpha_nonneg slack_nonneg])
  have unfold: "anchor_step alpha (anchor_state alpha j) =
      anchor_state alpha (Suc j)"
    by (simp add: anchor_state_Suc)
  have chain: "W b (Suc j) \<le> anchor_state alpha (Suc j) +
      real j * (alpha * Kslack) + alpha * Kslack"
    using step mono shift unfold by linarith
  have count: "real (Suc j) * (alpha * Kslack) =
      real j * (alpha * Kslack) + alpha * Kslack"
    by (simp add: algebra_simps add_divide_distrib)
  show ?case using chain count by linarith
qed

theorem aw_anchor_weight_log_bound:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and alpha_le: "alpha \<le> 4"
  shows "W b n \<le> ln (1 + real n * (exp alpha - 1)) + real n * (alpha * Kslack)"
proof -
  have alpha_nonneg: "0 \<le> alpha" using eta_pos eps_pos by simp
  have compare: "W b n \<le> anchor_state alpha n + real n * (alpha * Kslack)"
    by (rule aw_anchor_weight_le[OF anchor alpha_le order_refl])
  have logarithmic: "anchor_state alpha n \<le> ln (1 + real n * (exp alpha - 1))"
    by (rule anchor_log_bound[OF alpha_nonneg])
  show ?thesis using compare logarithmic by linarith
qed

abbreviation Hanchor where
  "Hanchor n \<equiv> ln (1 + real n * (exp alpha - 1)) + real n * (alpha * Kslack)"

theorem aw_anchor_tail_inversion_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "alpha \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "W b (n+m) < 0"
proof -
  have bound: "W b n \<le> Hanchor n"
    by (rule aw_anchor_weight_log_bound[OF anchor alpha_le])
  show ?thesis
    by (rule aw_anchor_tail_inversion[OF anchor tail bound burn_length
          burn_momentum takeover])
qed

corollary aw_attack_metrics_explicit:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and alpha_le: "alpha \<le> 4"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "Hanchor n + real J * (2*eta/eps) -
        real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p (W b (n+m)) = 1-p"
    and "clean_test_auc p (W b (n+m)) = p"
proof -
  have negative: "W b (n+m) < 0"
    by (rule aw_anchor_tail_inversion_explicit[where b=b and n=n and m=m
          and J=J, OF anchor tail alpha_le burn_length burn_momentum takeover])
  show "clean_test_risk p (W b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p (W b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

section \<open>Interval drift from a prefix discrepancy bound\<close>

lemma aw_bema_step_diff:
  "Bema b (Suc i) - bool_value (b i) =
    beta1 * (Bema b i - Bema b (Suc i)) / (1-beta1)"
proof -
  have rec: "Bema b (Suc i) = beta1 * Bema b i + (1-beta1) * bool_value (b i)"
    by simp
  have ne: "1 - beta1 \<noteq> 0" using beta1_lt by simp
  show ?thesis using rec ne by (simp add: field_simps)
qed

lemma aw_bema_interval_sum:
  assumes uv: "u \<le> v"
  shows "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
    beta1 * (Bema b u - Bema b v) / (1-beta1)"
  using uv
proof (induction v)
  case 0
  then show ?case by simp
next
  case (Suc v)
  show ?case
  proof (cases "u \<le> v")
    case True
    have split: "(\<Sum>i=u..<Suc v. Bema b (Suc i) - bool_value (b i)) =
        (\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) +
        (Bema b (Suc v) - bool_value (b v))"
      using True by simp
    have ih: "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
        beta1 * (Bema b u - Bema b v) / (1-beta1)"
      by (rule Suc.IH) (use True in simp)
    have last: "Bema b (Suc v) - bool_value (b v) =
        beta1 * (Bema b v - Bema b (Suc v)) / (1-beta1)"
      by (rule aw_bema_step_diff)
    have merge: "beta1 * (Bema b u - Bema b v) / (1-beta1) +
        beta1 * (Bema b v - Bema b (Suc v)) / (1-beta1) =
        beta1 * (Bema b u - Bema b (Suc v)) / (1-beta1)"
      by (rule real_scaled_telescope)
    show ?thesis using split ih last merge by simp
  next
    case False
    then have "u = Suc v" using Suc.prems by simp
    then show ?thesis by simp
  qed
qed

lemma aw_bema_interval_lower:
  assumes uv: "u \<le> v"
  shows "(\<Sum>i=u..<v. bool_value (b i)) - beta1/(1-beta1) \<le>
    (\<Sum>i=u..<v. Bema b (Suc i))"
proof -
  have telescope: "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
      beta1 * (Bema b u - Bema b v) / (1-beta1)"
    by (rule aw_bema_interval_sum[OF uv])
  have split: "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
      (\<Sum>i=u..<v. Bema b (Suc i)) - (\<Sum>i=u..<v. bool_value (b i))"
    by (simp add: sum_subtractf)
  have power: "0 \<le> beta1^v \<and> beta1^v \<le> 1"
    by (rule aw_power_bounds) (use beta1_nonneg beta1_lt in auto)
  have gap_low: "Bema b u - Bema b v \<ge> -1"
    using aw_bema_bounds(1)[of b u] aw_bema_bounds(2)[of b v] power
    by simp
  have scale_nonneg: "0 \<le> beta1 / (1-beta1)"
    using beta1_nonneg beta1_lt by simp
  have bounded: "- (beta1/(1-beta1)) \<le>
      beta1 * (Bema b u - Bema b v) / (1-beta1)"
  proof -
    have factored: "beta1 * (Bema b u - Bema b v) / (1-beta1) =
        (beta1/(1-beta1)) * (Bema b u - Bema b v)"
      by simp
    have monotone: "(beta1/(1-beta1)) * (-1) \<le>
        (beta1/(1-beta1)) * (Bema b u - Bema b v)"
      by (rule mult_left_mono[OF gap_low scale_nonneg])
    show ?thesis using factored monotone by simp
  qed
  show ?thesis using telescope split bounded by linarith
qed

lemma aw_step_drift_lower:
  assumes wk: "W b k \<le> delta"
  shows "eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
      eta * Kslack / eps - eta * (1 - ZH b (Suc k)) / eps \<le>
    W b (Suc k) - W b k"
proof -
  have dp: "0 < D b (Suc k)" by (rule aw_den_positive)
  have dlow: "eps \<le> D b (Suc k)" by (rule aw_den_bounds(1))
  have dhigh: "D b (Suc k) \<le> 1+eps" by (rule aw_den_bounds(2))
  have track: "abs (MH b (Suc k) - (sigmoid (W b k) - ZH b (Suc k))) \<le> Kslack"
    by (rule aw_moment_track)
  have upper: "MH b (Suc k) \<le> sigmoid (W b k) - ZH b (Suc k) + Kslack"
    using track by (simp add: abs_le_iff)
  have identity: "- (sigmoid (W b k) - ZH b (Suc k) + Kslack) =
      sigmoid (- W b k) - (1 - ZH b (Suc k)) - Kslack"
    by (simp add: sigmoid_neg_identity)
  have negate: "sigmoid (- W b k) - (1 - ZH b (Suc k)) - Kslack \<le>
      - MH b (Suc k)"
    using upper identity by linarith
  have step: "eta * (sigmoid (- W b k) - (1 - ZH b (Suc k)) - Kslack) \<le>
      eta * (- MH b (Suc k))"
    by (rule mult_left_mono[OF negate]) (use eta_pos in simp)
  have div_mono: "eta * (sigmoid (- W b k) - (1 - ZH b (Suc k)) - Kslack) /
        D b (Suc k) \<le> eta * (- MH b (Suc k)) / D b (Suc k)"
    by (rule divide_right_mono[OF step]) (use dp in simp)
  have split: "eta * (sigmoid (- W b k) - (1 - ZH b (Suc k)) - Kslack) /
        D b (Suc k) =
      eta * sigmoid (- W b k) / D b (Suc k) -
      eta * (1 - ZH b (Suc k)) / D b (Suc k) -
      eta * Kslack / D b (Suc k)"
    by (rule real_scaled_split)
  have sig_mono: "sigmoid (-delta) \<le> sigmoid (- W b k)"
    using sigmoid_difference_bounds(1)[of "-delta" "- W b k"] wk by simp
  have num: "eta * sigmoid (-delta) \<le> eta * sigmoid (- W b k)"
    by (rule mult_left_mono[OF sig_mono]) (use eta_pos in simp)
  have num_nonneg: "0 \<le> eta * sigmoid (-delta)"
    using sigmoid_pos[of "-delta"] eta_pos by simp
  have den: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (-delta) / D b (Suc k)"
  proof (rule divide_left_mono[OF dhigh num_nonneg])
    show "0 < (1+eps) * D b (Suc k)" using dp eps_pos by simp
  qed
  have num_div: "eta * sigmoid (-delta) / D b (Suc k) \<le>
      eta * sigmoid (- W b k) / D b (Suc k)"
    by (rule divide_right_mono[OF num]) (use dp in simp)
  have a_low: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (- W b k) / D b (Suc k)"
    using den num_div by linarith
  have zh_le: "ZH b (Suc k) \<le> 1" by (rule aw_zh_bounds(2))
  have b_low: "eta * (1 - ZH b (Suc k)) / D b (Suc k) \<le>
      eta * (1 - ZH b (Suc k)) / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * (1 - ZH b (Suc k))"
      by (rule mult_nonneg_nonneg) (use zh_le eta_pos in auto)
    show "0 < D b (Suc k) * eps" using dp eps_pos by simp
  qed
  have c_low: "eta * Kslack / D b (Suc k) \<le> eta * Kslack / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * Kslack"
      by (rule mult_nonneg_nonneg) (use eta_pos aw_slack_nonneg in auto)
    show "0 < D b (Suc k) * eps" using dp eps_pos by simp
  qed
  have decay_bound: "eta * decay * W b k \<le> eta * decay * delta"
    by (rule mult_left_mono[OF wk]) (use eta_pos decay_nonneg in simp)
  have expand: "(1 - eta*decay) * W b k = W b k - eta*decay*W b k"
    by (simp add: algebra_simps)
  have rec: "W b (Suc k) - W b k =
      - (eta*decay*W b k) - eta * MH b (Suc k) / D b (Suc k)"
    using aw_w_rec[of b k] expand by linarith
  have negdiv: "eta * (- MH b (Suc k)) / D b (Suc k) =
      - (eta * MH b (Suc k) / D b (Suc k))"
    by simp
  show ?thesis
    using rec div_mono split a_low b_low c_low decay_bound negdiv
    by linarith
qed

lemma aw_zh_ge_bema:
  "Bema b (Suc k) \<le> ZH b (Suc k)"
proof -
  have pos: "0 < 1 - beta1^(Suc k)" by (rule aw_bias_positive)
  have power: "0 \<le> beta1^(Suc k) \<and> beta1^(Suc k) \<le> 1"
    by (rule aw_power_bounds) (use beta1_nonneg beta1_lt in auto)
  have le_one: "1 - beta1^(Suc k) \<le> 1" using power by simp
  have nonneg: "0 \<le> Bema b (Suc k)" by (rule aw_bema_bounds(1))
  have scaled: "Bema b (Suc k) * (1 - beta1^(Suc k)) \<le> Bema b (Suc k) * 1"
    by (rule mult_left_mono[OF le_one nonneg])
  show ?thesis using scaled pos power
    by (simp add: mult.commute pos_le_divide_eq)
qed

lemma aw_interval_drift:
  assumes uv: "u \<le> v" and vN: "v \<le> N"
    and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> W b i \<le> delta"
    and disc: "\<And>k. k \<le> N \<Longrightarrow>
      abs ((\<Sum>i<k. bool_value (b i)) - p * real k) \<le> Dsc"
  shows "real (v-u) * (eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
        eta * Kslack / eps - eta * (1-p) / eps) -
      (eta/eps) * (2*Dsc + beta1/(1-beta1)) \<le> W b v - W b u"
proof -
  let ?C = "eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
      eta * Kslack / eps"
  let ?t = "\<lambda>i. eta * (1 - ZH b (Suc i)) / eps"
  have telescope: "(\<Sum>i=u..<v. W b (Suc i) - W b i) = W b v - W b u"
    by (rule sum_Suc_diff'[OF uv])
  have stepwise: "(\<Sum>i=u..<v. ?C - ?t i) \<le> (\<Sum>i=u..<v. W b (Suc i) - W b i)"
  proof (rule sum_mono)
    fix i
    assume i: "i \<in> {u..<v}"
    have wi: "W b i \<le> delta" using pre i by simp
    show "?C - ?t i \<le> W b (Suc i) - W b i"
      using aw_step_drift_lower[OF wi] by simp
  qed
  have split: "(\<Sum>i=u..<v. ?C - ?t i) = real (v-u) * ?C - (\<Sum>i=u..<v. ?t i)"
    by (simp add: sum_subtractf)
  have tsum: "(\<Sum>i=u..<v. ?t i) =
      (eta/eps) * (\<Sum>i=u..<v. (1 - ZH b (Suc i)))"
    by (simp add: sum_distrib_left)
  have zh_sum: "(\<Sum>i=u..<v. Bema b (Suc i)) \<le> (\<Sum>i=u..<v. ZH b (Suc i))"
    by (rule sum_mono) (use aw_zh_ge_bema in simp)
  have bema_low: "(\<Sum>i=u..<v. bool_value (b i)) - beta1/(1-beta1) \<le>
      (\<Sum>i=u..<v. Bema b (Suc i))"
    by (rule aw_bema_interval_lower[OF uv])
  have prefix_split: "(\<Sum>i=0..<u. bool_value (b i)) +
      (\<Sum>i=u..<v. bool_value (b i)) = (\<Sum>i=0..<v. bool_value (b i))"
    by (rule sum.atLeastLessThan_concat) (use uv in auto)
  have prefix_u: "(\<Sum>i=0..<u. bool_value (b i)) = (\<Sum>i<u. bool_value (b i))"
    by (simp add: atLeast0LessThan)
  have prefix_v: "(\<Sum>i=0..<v. bool_value (b i)) = (\<Sum>i<v. bool_value (b i))"
    by (simp add: atLeast0LessThan)
  have du: "abs ((\<Sum>i<u. bool_value (b i)) - p * real u) \<le> Dsc"
    by (rule disc) (use uv vN in simp)
  have dv: "abs ((\<Sum>i<v. bool_value (b i)) - p * real v) \<le> Dsc"
    by (rule disc) (use vN in simp)
  have du_le: "(\<Sum>i<u. bool_value (b i)) \<le> p * real u + Dsc"
    using du by (simp add: abs_le_iff)
  have dv_ge: "p * real v - Dsc \<le> (\<Sum>i<v. bool_value (b i))"
    using dv by (simp add: abs_le_iff)
  have pdiff: "p * real (v-u) = p * real v - p * real u"
    using uv by (simp add: algebra_simps)
  have count_low: "p * real (v-u) - 2*Dsc \<le> (\<Sum>i=u..<v. bool_value (b i))"
    using prefix_split prefix_u prefix_v du_le dv_ge pdiff by linarith
  have expand: "(\<Sum>i=u..<v. (1 - ZH b (Suc i))) =
      real (v-u) - (\<Sum>i=u..<v. ZH b (Suc i))"
    by (simp add: sum_subtractf)
  have one_minus: "(\<Sum>i=u..<v. (1 - ZH b (Suc i))) \<le>
      real (v-u) - (p * real (v-u) - 2*Dsc) + beta1/(1-beta1)"
    using expand zh_sum bema_low count_low by linarith
  have scale_nonneg: "0 \<le> eta/eps" using eta_pos eps_pos by simp
  have scaled: "(eta/eps) * (\<Sum>i=u..<v. (1 - ZH b (Suc i))) \<le>
      (eta/eps) * (real (v-u) - (p * real (v-u) - 2*Dsc) + beta1/(1-beta1))"
    by (rule mult_left_mono[OF one_minus scale_nonneg])
  have regroup: "(eta/eps) *
        (real (v-u) - (p * real (v-u) - 2*Dsc) + beta1/(1-beta1)) =
      real (v-u) * (eta * (1-p) / eps) +
      (eta/eps) * (2*Dsc + beta1/(1-beta1))"
  proof -
    have base: "(eta/eps) *
        (real (v-u) - (p * real (v-u) - 2*Dsc) + beta1/(1-beta1)) =
      (eta/eps) * (real (v-u) - p * real (v-u)) +
      (eta/eps) * (2*Dsc + beta1/(1-beta1))"
      by (simp add: algebra_simps)
    have lead: "(eta/eps) * (real (v-u) - p * real (v-u)) =
        real (v-u) * (eta * (1-p) / eps)"
      by (simp add: algebra_simps diff_divide_distrib)
    show ?thesis using base lead by simp
  qed
  have distrib: "real (v-u) * (eta * sigmoid (-delta) / (1+eps) -
        eta * decay * delta - eta * Kslack / eps - eta * (1-p) / eps) =
      real (v-u) * ?C - real (v-u) * (eta * (1-p) / eps)"
    by (simp add: algebra_simps)
  show ?thesis
    using telescope stepwise split tsum scaled regroup distrib by argo
qed

abbreviation Adrift where
  "Adrift delta p \<equiv> eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
    eta * Kslack / eps - eta * (1-p) / eps"
abbreviation Edrift where
  "Edrift Dsc \<equiv> (eta/eps) * (2*Dsc + beta1/(1-beta1))"

theorem aw_prefix_discrepancy_positive:
  assumes Npos: "0 < N"
    and disc: "\<And>k. k \<le> N \<Longrightarrow>
      abs ((\<Sum>i<k. bool_value (b i)) - p * real k) \<le> Dsc"
    and drift_nonneg: "0 \<le> Adrift delta p"
    and landing: "0 < delta - 2*eta/eps - Edrift Dsc"
    and total: "0 < Adrift delta p * real N - Edrift Dsc"
  shows "0 < W b N"
proof -
  have disc_zero: "abs ((\<Sum>i<0. bool_value (b i)) - p * real 0) \<le> Dsc"
    by (rule disc) simp
  have Dsc_nonneg: "0 \<le> Dsc" using disc_zero by simp
  have slack_nonneg: "0 \<le> Edrift Dsc"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> eta/eps" using eta_pos eps_pos by simp
    show "0 \<le> 2*Dsc + beta1/(1-beta1)"
      using Dsc_nonneg beta1_nonneg beta1_lt by simp
  qed
  show ?thesis
  proof (rule aw_interval_barrier_positive[where w = "W b" and N = N
      and A = "Adrift delta p" and B = "Edrift Dsc"
      and S = "2*eta/eps" and r = delta])
    show "0 < N" by (rule Npos)
    show "W b 0 = 0" by (simp add: aw_zero_def)
    show "0 \<le> Adrift delta p" by (rule drift_nonneg)
    show "0 \<le> Edrift Dsc" by (rule slack_nonneg)
    show "0 < delta - 2*eta/eps - Edrift Dsc" by (rule landing)
    show "0 < Adrift delta p * real N - Edrift Dsc" by (rule total)
    show "abs (W b (Suc i) - W b i) \<le> 2*eta/eps" if "i < N" for i
      by (rule aw_jump_bound)
    show "Adrift delta p * real (v-u) - Edrift Dsc \<le> W b v - W b u"
      if uv: "u < v" and vN: "v \<le> N"
        and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> W b i \<le> delta" for u v
    proof -
      have drift: "real (v-u) * Adrift delta p - Edrift Dsc \<le> W b v - W b u"
        by (rule aw_interval_drift[where u=u and v=v and N=N and b=b
              and delta=delta and p=p and Dsc=Dsc])
          (use uv vN pre disc in auto)
      show ?thesis using drift by (simp add: mult.commute)
    qed
  qed
qed

text \<open>
  The finite-population prefix concentration of the repository now discharges
  the discrepancy premise, so the benign conclusion holds with explicit
  confidence for a uniformly random presentation order.
\<close>

theorem aw_random_order_benign_probability:
  fixes conf delta :: real
  assumes N_positive: "0 < N" and sample_size: "n \<le> N"
    and conf_positive: "0 < conf" and conf_at_most_one: "conf \<le> 1"
    and drift_nonneg: "0 \<le> Adrift delta (real n / real N)"
    and landing: "0 < delta - 2*eta/eps -
      Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
    and total: "0 < Adrift delta (real n / real N) * real N -
      Edrift (sqrt (real N / 2 * ln (2 * real N / conf)))"
  shows "1 - conf \<le> uniform_probability (binary_orders n N)
    {xs. 0 < W (\<lambda>i. xs ! i) N}"
proof -
  let ?Omega = "binary_orders n N"
  let ?u = "sqrt (real N / 2 * ln (2 * real N / conf))"
  let ?bad = "{xs. ?u \<le> binary_max_centered_prefix n N xs}"
  let ?good = "{xs. 0 < W (\<lambda>i. xs ! i) N}"
  have bad_bound: "uniform_probability ?Omega ?bad \<le> conf"
    by (rule uniform_binary_order_max_prefix_confidence[OF N_positive
          sample_size conf_positive conf_at_most_one])
  have Omega_nonempty: "?Omega \<noteq> {}"
    by (rule binary_orders_nonempty[OF sample_size])
  have complement_probability:
    "uniform_probability ?Omega (- ?bad) =
      1 - uniform_probability ?Omega ?bad"
    by (rule uniform_probability_complement[OF finite_binary_orders
          Omega_nonempty])
  have complement_lower: "1 - conf \<le> uniform_probability ?Omega (- ?bad)"
    using bad_bound complement_probability by linarith
  have event_subset: "?Omega \<inter> (- ?bad) \<subseteq> ?good"
  proof
    fix xs
    assume member: "xs \<in> ?Omega \<inter> (- ?bad)"
    have xs_order: "xs \<in> binary_orders n N" using member by simp
    have prefix_good: "binary_max_centered_prefix n N xs < ?u"
      using member by simp
    have disc: "abs ((\<Sum>i<k. bool_value (xs ! i)) -
        (real n / real N) * real k) \<le> ?u" if kN: "k \<le> N" for k
    proof -
      have prefix_eq: "prefix_sum (binary_innovation (real n / real N) xs) k =
          (\<Sum>i<k. bool_value (xs ! i)) - (real n / real N) * real k"
        by (simp add: prefix_sum_def binary_innovation_def sum_subtractf
              mult.commute)
      have le_max: "abs (prefix_sum (binary_innovation (real n / real N) xs) k)
          \<le> binary_max_centered_prefix n N xs"
        by (rule binary_innovation_prefix_le_max[OF N_positive sample_size
              xs_order kN])
      show ?thesis using prefix_eq le_max prefix_good by simp
    qed
    have positive: "0 < W (\<lambda>i. xs ! i) N"
      by (rule aw_prefix_discrepancy_positive[where b = "\<lambda>i. xs ! i"
            and N = N and p = "real n / real N" and Dsc = ?u
            and delta = delta])
        (use N_positive disc drift_nonneg landing total in auto)
    show "xs \<in> ?good" using positive by simp
  qed
  have event_mono:
    "uniform_probability ?Omega (?Omega \<inter> (- ?bad)) \<le>
      uniform_probability ?Omega ?good"
    by (rule uniform_probability_mono[OF finite_binary_orders event_subset])
  have normalized_complement:
    "uniform_probability ?Omega (?Omega \<inter> (- ?bad)) =
      uniform_probability ?Omega (- ?bad)"
    unfolding uniform_probability_def by (simp add: Int_assoc)
  show ?thesis
    using complement_lower event_mono normalized_complement by linarith
qed

end

end
