theory Adam_Core
  imports "../Order_Only_Inversion_Extensions"
begin

section \<open>Exact bias-corrected Adam and AdamW\<close>

text \<open>
  Shared exact core for the certified Adam and AdamW optimizer theories.
  The clock is the global iteration index. Moments are never reset at the
  Anchor/Tail boundary. Setting decay = 0 gives Adam without coupled L2
  regularization. The second moment is updated, not frozen. Arithmetic is real.
\<close>

record aw_state =
  aw_weight :: real
  aw_first :: real
  aw_second :: real

definition aw_zero :: aw_state where
  "aw_zero = \<lparr>aw_weight = 0, aw_first = 0, aw_second = 0\<rparr>"

definition aw_step ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   nat \<Rightarrow> bool \<Rightarrow> aw_state \<Rightarrow> aw_state" where
  "aw_step eta beta1 beta2 eps decay t b z =
    (let g = sigmoid (aw_weight z) - bool_value b;
         m = beta1 * aw_first z + (1 - beta1) * g;
         v = beta2 * aw_second z + (1 - beta2) * g^2;
         mh = m / (1 - beta1^t);
         vh = v / (1 - beta2^t)
     in \<lparr>aw_weight = (1 - eta * decay) * aw_weight z -
                        eta * mh / (sqrt vh + eps),
            aw_first = m, aw_second = v\<rparr>)"

primrec aw_run ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> aw_state" where
  "aw_run eta beta1 beta2 eps decay b 0 = aw_zero"
| "aw_run eta beta1 beta2 eps decay b (Suc k) =
     aw_step eta beta1 beta2 eps decay (Suc k) (b k)
       (aw_run eta beta1 beta2 eps decay b k)"

definition aw_list_run ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   bool list \<Rightarrow> aw_state" where
  "aw_list_run eta beta1 beta2 eps decay xs =
    aw_run eta beta1 beta2 eps decay (\<lambda>i. xs ! i) (length xs)"

lemma aw_clean_gradient_bridge:
  assumes "s = 1 \<or> s = -1" and "t = 1 \<or> t = -1"
  shows "logistic_example_gradient s (clean_label s t) w =
    sigmoid w - bool_value (t = 1)"
  using assms
  by (auto simp: logistic_example_gradient_def clean_label_def
        bool_value_def sigmoid_neg_identity)

section \<open>Elementary geometric and iteration lemmas\<close>

lemma aw_power_bounds:
  fixes beta :: real
  assumes "0 \<le> beta" "beta \<le> 1"
  shows "0 \<le> beta^n \<and> beta^n \<le> 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have lo: "0 \<le> beta * beta^n"
    using assms Suc.IH by (intro mult_nonneg_nonneg) auto
  have hi: "beta * beta^n \<le> 1"
  proof -
    have "beta * beta^n \<le> beta * 1"
      by (rule mult_left_mono) (use assms Suc.IH in auto)
    then show ?thesis using assms by simp
  qed
  show ?case using lo hi by simp
qed

lemma aw_bias_bounds:
  fixes beta :: real
  assumes "0 \<le> beta" "beta < 1"
  shows "0 < 1 - beta^(Suc n) \<and> 1 - beta^(Suc n) \<le> 1"
proof -
  have b: "0 \<le> beta^n \<and> beta^n \<le> 1"
    by (rule aw_power_bounds) (use assms in auto)
  have scaled: "beta * beta^n \<le> beta"
    using mult_left_mono[OF b[THEN conjunct2] assms(1)] by simp
  have nonneg: "0 \<le> beta^(Suc n)"
    using aw_power_bounds[of beta "Suc n"] assms by auto
  show ?thesis using scaled nonneg assms by (simp only: power_Suc) linarith
qed

lemma aw_power_antimono:
  fixes beta :: real
  assumes "0 \<le> beta" "beta \<le> 1" "i \<le> j"
  shows "beta^j \<le> beta^i"
proof -
  have bounds: "0 \<le> beta^i" "beta^(j-i) \<le> 1"
    using aw_power_bounds[OF assms(1,2)] by auto
  have split: "beta^j = beta^i * beta^(j-i)"
    using assms(3) by (simp flip: power_add)
  show ?thesis unfolding split
    using mult_left_mono[OF bounds(2) bounds(1)] by simp
qed

lemma aw_affine_iteration_upper:
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
  have step_n: "f (Suc n) \<le> f n + d"
    by (rule Suc.prems) simp
  show ?case using ih step_n
    by (simp add: algebra_simps)
qed

primrec aw_ema :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "aw_ema beta x 0 = 0"
| "aw_ema beta x (Suc k) = beta * aw_ema beta x k + (1-beta) * x k"

definition aw_corrected_ema ::
  "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "aw_corrected_ema beta x k = aw_ema beta x k / (1-beta^k)"

lemma aw_ema_constant:
  "aw_ema beta (\<lambda>i. c) n = c * (1-beta^n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have identity:
    "beta * (c * (1 - beta^n)) + (1-beta) * c =
      c * (1 - beta * beta^n)"
    by algebra
  show ?case using Suc.IH identity
    by simp
qed

lemma aw_ema_add:
  "aw_ema beta (\<lambda>i. x i + y i) n =
    aw_ema beta x n + aw_ema beta y n"
  by (induction n) (simp_all add: algebra_simps)

lemma aw_ema_mono:
  assumes beta: "0 \<le> beta" "beta \<le> 1"
    and pointwise: "\<And>i. i < n \<Longrightarrow> x i \<le> y i"
  shows "aw_ema beta x n \<le> aw_ema beta y n"
  using pointwise
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "aw_ema beta x n \<le> aw_ema beta y n"
    by (rule Suc.IH) (use Suc.prems in auto)
  have a: "beta * aw_ema beta x n \<le> beta * aw_ema beta y n"
    by (rule mult_left_mono[OF ih beta(1)])
  have b: "(1-beta) * x n \<le> (1-beta) * y n"
    by (rule mult_left_mono) (use Suc.prems beta in auto)
  show ?case using a b by (simp only: aw_ema.simps)
qed

lemma aw_ema_abs_bound:
  assumes beta: "0 \<le> beta" "beta \<le> 1"
    and x: "\<And>i. i < n \<Longrightarrow> abs (x i) \<le> 1"
  shows "abs (aw_ema beta x n) \<le> 1-beta^n"
proof -
  have lo: "aw_ema beta (\<lambda>i. -1) n \<le> aw_ema beta x n"
  proof (rule aw_ema_mono[OF beta])
    fix i
    assume "i < n"
    from x[OF this] show "-1 \<le> x i"
      by (simp add: abs_le_iff)
  qed
  have hi: "aw_ema beta x n \<le> aw_ema beta (\<lambda>i. 1) n"
  proof (rule aw_ema_mono[OF beta])
    fix i
    assume "i < n"
    from x[OF this] show "x i \<le> 1"
      by (simp add: abs_le_iff)
  qed
  show ?thesis using lo hi
    by (simp add: aw_ema_constant abs_le_iff)
qed

section \<open>Parameter contract and exact trajectory bounds\<close>

locale aw_parameters =
  fixes eta beta1 beta2 eps decay :: real
  assumes eta_pos: "0 < eta"
    and beta1_nonneg: "0 \<le> beta1" and beta1_lt: "beta1 < 1"
    and beta2_nonneg: "0 \<le> beta2" and beta2_lt: "beta2 < 1"
    and eps_pos: "0 < eps"
    and decay_nonneg: "0 \<le> decay"
    and decay_step: "eta * decay \<le> 1"
begin

abbreviation S where "S b k \<equiv> aw_run eta beta1 beta2 eps decay b k"
abbreviation W where "W b k \<equiv> aw_weight (S b k)"
abbreviation M where "M b k \<equiv> aw_first (S b k)"
abbreviation V where "V b k \<equiv> aw_second (S b k)"
abbreviation G where "G b k \<equiv> sigmoid (W b k) - bool_value (b k)"
abbreviation MH where "MH b k \<equiv> M b k / (1-beta1^k)"
abbreviation VH where "VH b k \<equiv> V b k / (1-beta2^k)"
abbreviation D where "D b k \<equiv> sqrt (VH b k) + eps"

lemma aw_initial [simp]:
  "W b 0 = 0" "M b 0 = 0" "V b 0 = 0"
  by (simp_all add: aw_zero_def)

lemma aw_m_rec:
  "M b (Suc k) = beta1 * M b k + (1-beta1) * G b k"
  by (simp add: aw_step_def Let_def)

lemma aw_v_rec:
  "V b (Suc k) = beta2 * V b k + (1-beta2) * (G b k)^2"
  by (simp add: aw_step_def Let_def)

lemma aw_w_rec:
  "W b (Suc k) = (1-eta*decay) * W b k -
    eta * MH b (Suc k) / D b (Suc k)"
  by (simp add: aw_step_def Let_def)

lemma aw_m_ema:
  "M b k = aw_ema beta1 (G b) k"
proof (induction k)
  case 0
  then show ?case by (simp add: aw_zero_def)
next
  case (Suc k)
  show ?case using Suc.IH
    by (simp only: aw_m_rec aw_ema.simps)
qed

lemma aw_v_ema:
  "V b k = aw_ema beta2 (\<lambda>i. (G b i)^2) k"
proof (induction k)
  case 0
  then show ?case by (simp add: aw_zero_def)
next
  case (Suc k)
  show ?case using Suc.IH
    by (simp only: aw_v_rec aw_ema.simps)
qed

lemma aw_gradient_bound:
  "abs (G b k) \<le> 1"
  by (rule binary_logistic_gradient_abs_le_one)

lemma aw_m_bound:
  "abs (M b k) \<le> 1-beta1^k"
  unfolding aw_m_ema
  by (rule aw_ema_abs_bound)
    (use beta1_nonneg beta1_lt aw_gradient_bound in auto)

lemma aw_v_bounds:
  "0 \<le> V b k" "V b k \<le> 1-beta2^k"
proof -
  have bounds: "0 \<le> (G b i)^2 \<and> (G b i)^2 \<le> 1" for i
  proof
    show "0 \<le> (G b i)^2" by simp
    have "(abs (G b i))^2 \<le> (1::real)^2"
      by (rule power_mono[OF aw_gradient_bound abs_ge_zero])
    then show "(G b i)^2 \<le> 1" by simp
  qed
  have lo: "aw_ema beta2 (\<lambda>i. 0) k \<le>
      aw_ema beta2 (\<lambda>i. (G b i)^2) k"
    by (rule aw_ema_mono)
      (use beta2_nonneg beta2_lt bounds in auto)
  have hi: "aw_ema beta2 (\<lambda>i. (G b i)^2) k \<le>
      aw_ema beta2 (\<lambda>i. 1) k"
    by (rule aw_ema_mono)
      (use beta2_nonneg beta2_lt bounds in auto)
  show "0 \<le> V b k" "V b k \<le> 1-beta2^k"
    using lo hi by (simp_all add: aw_v_ema aw_ema_constant)
qed

lemma aw_mhat_bound:
  "abs (MH b (Suc k)) \<le> 1"
proof -
  have rho: "0 < 1-beta1^(Suc k)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by blast
  show ?thesis using aw_m_bound[of b "Suc k"] rho
    by (simp add: divide_le_eq)
qed

lemma aw_vhat_bounds:
  "0 \<le> VH b (Suc k)" "VH b (Suc k) \<le> 1"
proof -
  have rho: "0 < 1-beta2^(Suc k)"
    using aw_bias_bounds[OF beta2_nonneg beta2_lt, of k] by blast
  show "0 \<le> VH b (Suc k)" "VH b (Suc k) \<le> 1"
    using aw_v_bounds[of b "Suc k"] rho
    by (simp_all add: divide_le_eq)
qed

lemma aw_den_bounds:
  "eps \<le> D b (Suc k)" "D b (Suc k) \<le> 1+eps"
proof -
  have lo: "0 \<le> sqrt (VH b (Suc k))"
    by (rule real_sqrt_ge_zero[OF aw_vhat_bounds(1)])
  have hi: "sqrt (VH b (Suc k)) \<le> sqrt 1"
    by (rule real_sqrt_le_mono[OF aw_vhat_bounds(2)])
  show "eps \<le> D b (Suc k)" "D b (Suc k) \<le> 1+eps"
    using lo hi by simp_all
qed

lemma aw_den_positive:
  "0 < D b (Suc k)"
  using aw_den_bounds(1)[of b k] eps_pos by linarith

lemma aw_direction_bound:
  "abs (MH b (Suc k) / D b (Suc k)) \<le> 1/eps"
proof -
  have dp: "0 < D b (Suc k)" by (rule aw_den_positive)
  have ratio: "1 \<le> D b (Suc k) / eps"
    using aw_den_bounds(1)[of b k] eps_pos
    by (simp add: le_divide_eq)
  have identity: "(1/eps) * D b (Suc k) = D b (Suc k) / eps"
    by algebra
  have scaled: "abs (MH b (Suc k)) \<le> (1/eps) * D b (Suc k)"
    using aw_mhat_bound[of b k] ratio identity by linarith
  have quotient: "abs (MH b (Suc k)) / D b (Suc k) \<le> 1/eps"
    using scaled dp by (simp only: divide_le_eq if_True)
  have ad: "abs (D b (Suc k)) = D b (Suc k)"
    by (rule abs_of_pos[OF dp])
  have rewrite: "abs (MH b (Suc k) / D b (Suc k)) =
      abs (MH b (Suc k)) / D b (Suc k)"
  proof -
    have "abs (MH b (Suc k) / D b (Suc k)) =
        abs (MH b (Suc k)) / abs (D b (Suc k))"
      by (rule abs_divide)
    then show ?thesis by (simp only: ad)
  qed
  show ?thesis using rewrite quotient by linarith
qed

lemma aw_decay_weight_bound:
  "decay * abs (W b k) \<le> 1/eps"
proof (induction k)
  case 0
  then show ?case using eps_pos by (simp add: aw_zero_def)
next
  case (Suc k)
  let ?q = "1-eta*decay"
  let ?u = "MH b (Suc k) / D b (Suc k)"
  have q0: "0 \<le> ?q" using decay_step by linarith
  have e0: "0 \<le> eta" using eta_pos by linarith
  have ub: "abs ?u \<le> 1/eps" by (rule aw_direction_bound)
  have rec: "W b (Suc k) = ?q * W b k - eta * ?u"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  have tri: "abs (W b (Suc k)) \<le> ?q * abs (W b k) + eta * abs ?u"
    using rec abs_triangle_ineq[of "?q * W b k" "-eta * ?u"] q0 e0
    by (simp add: abs_mult)
  have scaled: "decay * abs (W b (Suc k)) \<le>
      ?q * (decay * abs (W b k)) + eta * decay * abs ?u"
    using mult_left_mono[OF tri decay_nonneg] by (simp add: algebra_simps)
  have bound1: "?q * (decay * abs (W b k)) \<le> ?q * (1/eps)"
    by (rule mult_left_mono[OF Suc.IH q0])
  have factor_nonnegative: "0 \<le> eta * decay"
    by (rule mult_nonneg_nonneg[OF e0 decay_nonneg])
  have bound2: "eta * decay * abs ?u \<le> eta * decay * (1/eps)"
    by (rule mult_left_mono[OF ub factor_nonnegative])
  have identity: "?q * (1/eps) + eta * decay * (1/eps) = 1/eps"
    by algebra
  show ?case using scaled bound1 bound2 identity by linarith
qed

lemma aw_jump_bound:
  "abs (W b (Suc k) - W b k) \<le> 2*eta/eps"
proof -
  let ?u = "MH b (Suc k) / D b (Suc k)"
  have e0: "0 \<le> eta" using eta_pos by linarith
  have rec: "W b (Suc k) = (1-eta*decay) * W b k - eta * ?u"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  have identity: "W b (Suc k) - W b k =
      -eta * (decay * W b k) - eta * ?u"
    by (simp only: rec; algebra)
  have tri: "abs (W b (Suc k) - W b k) \<le>
      eta * (decay * abs (W b k)) + eta * abs ?u"
    using identity
      abs_triangle_ineq[of "-eta * (decay * W b k)" "-eta * ?u"]
      e0 decay_nonneg by (simp add: abs_mult)
  have a: "eta * (decay * abs (W b k)) \<le> eta * (1/eps)"
    by (rule mult_left_mono[OF aw_decay_weight_bound[of b k] e0])
  have c: "eta * abs ?u \<le> eta * (1/eps)"
    by (rule mult_left_mono[OF aw_direction_bound[of b k] e0])
  have final_identity: "eta * (1/eps) + eta * (1/eps) = 2*eta/eps"
    by algebra
  show ?thesis using tri a c final_identity by linarith
qed

lemma aw_prefix_weight_upper:
  "W b (n+j) \<le> W b n + real j * (2*eta/eps)"
proof -
  have step: "W b (n+Suc i) \<le> W b (n+i) + 2*eta/eps" for i
    using aw_jump_bound[of b "n+i"] by (simp add: abs_le_iff)
  show ?thesis
    using aw_affine_iteration_upper[where n=j and f="\<lambda>i. W b (n+i)" and d="2*eta/eps"] step
    by simp
qed

section \<open>Sign persistence on an exact Counterexample Tail\<close>

lemma aw_anchor_prefix:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
  shows "0 \<le> W b n \<and> M b n \<le> 0"
  using anchor
proof (induction n)
  case 0
  then show ?case by (simp add: aw_zero_def)
next
  case (Suc n)
  have ih: "0 \<le> W b n \<and> M b n \<le> 0"
    by (rule Suc.IH) (use Suc.prems in auto)
  have bn: "b n" by (rule Suc.prems) simp
  have g0: "G b n \<le> 0"
    using sigmoid_le_one[of "W b n"] bn by (simp add: bool_value_def)
  have a0: "beta1 * M b n \<le> 0"
    by (rule mult_nonneg_nonpos) (use beta1_nonneg ih in auto)
  have c0: "(1-beta1) * G b n \<le> 0"
    by (rule mult_nonneg_nonpos) (use beta1_lt g0 in auto)
  have m0: "M b (Suc n) \<le> 0"
    using a0 c0 by (simp only: aw_m_rec)
  have rho: "0 < 1-beta1^(Suc n)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of n] by blast
  have u0: "MH b (Suc n) / D b (Suc n) \<le> 0"
    using m0 rho aw_den_positive[of b n] by (simp add: divide_nonpos_nonneg)
  have q0: "0 \<le> (1-eta*decay) * W b n"
    by (rule mult_nonneg_nonneg) (use decay_step ih in auto)
  have eta0: "0 \<le> eta" using eta_pos by linarith
  have eu0: "eta * (MH b (Suc n) / D b (Suc n)) \<le> 0"
    by (rule mult_nonneg_nonpos[OF eta0 u0])
  have rec: "W b (Suc n) = (1-eta*decay) * W b n -
      eta * (MH b (Suc n) / D b (Suc n))"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  have w0: "0 \<le> W b (Suc n)"
    using rec q0 eu0 by linarith
  show ?case using w0 m0 by blast
qed

lemma aw_tail_negative_step:
  assumes tail: "\<not> b k" and wneg: "W b k < 0" and mnonneg: "0 \<le> M b k"
  shows "W b (Suc k) < 0 \<and> 0 < M b (Suc k)"
proof -
  have gp: "0 < G b k"
    using sigmoid_pos[of "W b k"] tail by (simp add: bool_value_def)
  have old: "0 \<le> beta1 * M b k"
    by (rule mult_nonneg_nonneg[OF beta1_nonneg mnonneg])
  have new: "0 < (1-beta1) * G b k"
    by (rule mult_pos_pos) (use beta1_lt gp in auto)
  have mp: "0 < M b (Suc k)" using old new by (simp only: aw_m_rec)
  have rho: "0 < 1-beta1^(Suc k)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by blast
  have up: "0 < MH b (Suc k) / D b (Suc k)"
    using mp rho aw_den_positive[of b k] by (intro divide_pos_pos) assumption
  have qwn: "(1-eta*decay) * W b k \<le> 0"
    by (rule mult_nonneg_nonpos) (use decay_step wneg in auto)
  have eup: "0 < eta * (MH b (Suc k) / D b (Suc k))"
    by (rule mult_pos_pos[OF eta_pos up])
  have rec: "W b (Suc k) = (1-eta*decay) * W b k -
      eta * (MH b (Suc k) / D b (Suc k))"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  have wp: "W b (Suc k) < 0"
    using rec qwn eup by linarith
  show ?thesis using wp mp by blast
qed

lemma aw_crossing_positive_moment:
  assumes w0: "0 \<le> W b k" and wn: "W b (Suc k) < 0"
  shows "0 < M b (Suc k)"
proof (rule ccontr)
  assume neg: "\<not> 0 < M b (Suc k)"
  have rho: "0 < 1-beta1^(Suc k)"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by blast
  have u0: "MH b (Suc k) / D b (Suc k) \<le> 0"
    using neg rho aw_den_positive[of b k] by (simp add: divide_nonpos_nonneg)
  have q0: "0 \<le> (1-eta*decay) * W b k"
    by (rule mult_nonneg_nonneg) (use decay_step w0 in auto)
  have eta0: "0 \<le> eta" using eta_pos by linarith
  have eu0: "eta * (MH b (Suc k) / D b (Suc k)) \<le> 0"
    by (rule mult_nonneg_nonpos[OF eta0 u0])
  have rec: "W b (Suc k) = (1-eta*decay) * W b k -
      eta * (MH b (Suc k) / D b (Suc k))"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  show False using wn rec q0 eu0 by linarith
qed

lemma aw_tail_negative_has_positive_moment:
  assumes start: "0 \<le> W b n"
    and tail: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)"
    and negative: "W b (n+j) < 0"
  shows "0 < M b (n+j)"
  using tail negative
proof (induction j)
  case 0
  then show ?case using start by simp
next
  case (Suc j)
  show ?case
  proof (cases "W b (n+j) < 0")
    case True
    have mp: "0 < M b (n+j)"
      by (rule Suc.IH) (use Suc.prems True in auto)
    have bn: "\<not> b (n+j)" by (rule Suc.prems(1)) simp
    have step: "W b (Suc (n+j)) < 0 \<and> 0 < M b (Suc (n+j))"
      by (rule aw_tail_negative_step[OF bn True]) (use mp in linarith)
    show ?thesis using step by simp
  next
    case False
    have w0: "0 \<le> W b (n+j)" using False by linarith
    show ?thesis
      using aw_crossing_positive_moment[OF w0] Suc.prems(2) by simp
  qed
qed

lemma aw_tail_all_nonnegative:
  assumes start: "0 \<le> W b n"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and final: "0 \<le> W b (n+m)"
  shows "\<forall>j\<le>m. 0 \<le> W b (n+j)"
  using tail final
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have prev: "0 \<le> W b (n+m)"
  proof (rule ccontr)
    assume "\<not> 0 \<le> W b (n+m)"
    then have wn: "W b (n+m) < 0" by linarith
    have mp: "0 < M b (n+m)"
      by (rule aw_tail_negative_has_positive_moment[OF start _ wn])
        (use Suc.prems in auto)
    have bn: "\<not> b (n+m)" by (rule Suc.prems(1)) simp
    have "W b (Suc (n+m)) < 0"
      using aw_tail_negative_step[OF bn wn] mp by auto
    then show False using Suc.prems(2) by simp
  qed
  have ih: "\<forall>j\<le>m. 0 \<le> W b (n+j)"
    by (rule Suc.IH) (use Suc.prems prev in auto)
  show ?case using ih Suc.prems(2) by (metis le_Suc_eq)
qed

lemma aw_tail_moment_lower:
  assumes tail: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)"
    and nonnegative: "\<And>i. i < j \<Longrightarrow> 0 \<le> W b (n+i)"
  shows "1/2 - (3/2)*beta1^j \<le> M b (n+j)"
  using tail nonnegative
proof (induction j)
  case 0
  have bpow: "0 \<le> beta1^n"
    using aw_power_bounds[of beta1 n] beta1_nonneg beta1_lt by auto
  have "-1 \<le> M b n" using aw_m_bound[of b n] bpow
    by (simp add: abs_le_iff)
  then show ?case by simp
next
  case (Suc j)
  have ih: "1/2 - (3/2)*beta1^j \<le> M b (n+j)"
    by (rule Suc.IH) (use Suc.prems in auto)
  have wn: "0 \<le> W b (n+j)" by (rule Suc.prems(2)) simp
  have bn: "\<not> b (n+j)" by (rule Suc.prems(1)) simp
  have gl: "1/2 \<le> G b (n+j)"
    using sigmoid_lower_bound[of 0 "W b (n+j)"] wn bn
    by (simp add: bool_value_def)
  have a: "beta1 * (1/2 - (3/2)*beta1^j) \<le> beta1 * M b (n+j)"
    by (rule mult_left_mono[OF ih beta1_nonneg])
  have c: "(1-beta1) * (1/2) \<le> (1-beta1) * G b (n+j)"
    by (rule mult_left_mono[OF gl]) (use beta1_lt in linarith)
  have sum: "beta1 * (1/2 - (3/2)*beta1^j) + (1-beta1) * (1/2) \<le>
      beta1 * M b (n+j) + (1-beta1) * G b (n+j)"
    using a c by linarith
  have identity: "beta1 * (1/2 - (3/2)*beta1^j) + (1-beta1) * (1/2) =
      1/2 - (3/2)*beta1^(Suc j)"
    by (simp only: power_Suc; algebra)
  have rec: "M b (n+Suc j) =
      beta1 * M b (n+j) + (1-beta1) * G b (n+j)"
    by (simp only: add_Suc_right aw_m_rec)
  show ?case using sum identity rec by linarith
qed

lemma aw_tail_quarter_descent:
  assumes w0: "0 \<le> W b k" and ml: "1/4 \<le> M b (Suc k)"
  shows "W b (Suc k) \<le> W b k - eta / (4*(1+eps))"
proof -
  have rho: "0 < 1-beta1^(Suc k)" "1-beta1^(Suc k) \<le> 1"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by auto
  have quarter_rho_raw: "(1/4) * (1-beta1^(Suc k)) \<le> (1/4) * 1"
    by (rule mult_left_mono[OF rho(2)]) simp
  have quarter_rho: "(1/4) * (1-beta1^(Suc k)) \<le> (1/4)"
    using quarter_rho_raw by simp
  have numerator: "(1/4) * (1-beta1^(Suc k)) \<le> M b (Suc k)"
    using quarter_rho ml by linarith
  have mh: "1/4 \<le> MH b (Suc k)"
    using numerator rho(1) by (simp only: le_divide_eq if_True)
  have dp: "0 < D b (Suc k)" by (rule aw_den_positive)
  have ep: "0 < 1+eps" using eps_pos by linarith
  have factor_nonnegative: "0 \<le> (1/4) / D b (Suc k)"
    using dp by simp
  have product: "((1/4) / D b (Suc k)) * D b (Suc k) \<le>
      ((1/4) / D b (Suc k)) * (1+eps)"
    by (rule mult_left_mono[OF aw_den_bounds(2) factor_nonnegative])
  have cancel: "((1/4) / D b (Suc k)) * D b (Suc k) = 1/4"
    using dp by simp
  have target: "1/4 \<le> ((1/4) / D b (Suc k)) * (1+eps)"
    using product cancel by linarith
  have q1: "(1/4) / (1+eps) \<le> (1/4) / D b (Suc k)"
    using target ep by (subst divide_le_eq) simp
  have q2: "(1/4) / D b (Suc k) \<le> MH b (Suc k) / D b (Suc k)"
    by (rule divide_right_mono[OF mh]) (use dp in linarith)
  have eq: "(1/4) / (1+eps) = 1/(4*(1+eps))"
    using ep by (simp add: divide_simps; algebra)
  have qraw: "(1/4) / (1+eps) \<le> MH b (Suc k) / D b (Suc k)"
    by (rule order_trans[OF q1 q2])
  have q: "1/(4*(1+eps)) \<le> MH b (Suc k) / D b (Suc k)"
    using qraw eq by simp
  have e0: "0 \<le> eta" using eta_pos by linarith
  have scaled: "eta/(4*(1+eps)) \<le> eta * (MH b (Suc k) / D b (Suc k))"
    using mult_left_mono[OF q e0] by simp
  have eta_decay_nonnegative: "0 \<le> eta*decay"
    by (rule mult_nonneg_nonneg[OF e0 decay_nonneg])
  have removed_nonnegative: "0 \<le> (eta*decay) * W b k"
    by (rule mult_nonneg_nonneg[OF eta_decay_nonnegative w0])
  have contraction_identity: "(1-eta*decay)*W b k =
      W b k - (eta*decay) * W b k"
    by algebra
  have contraction: "(1-eta*decay)*W b k \<le> W b k"
    using contraction_identity removed_nonnegative by linarith
  have rec: "W b (Suc k) = (1-eta*decay) * W b k -
      eta * (MH b (Suc k) / D b (Suc k))"
    by (simp only: aw_w_rec field_class.field_divide_inverse mult.assoc)
  show ?thesis using rec scaled contraction by linarith
qed

text \<open>
  This exact finite-step theorem is shared by Adam and AdamW. Its explicit
  anchor bound, burn-in length, and takeover inequality form the deterministic
  certificate consumed by both optimizer-specific entry theories.
\<close>

theorem aw_anchor_tail_inversion:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and anchor_bound: "W b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "beta1^J \<le> 1/6"
    and takeover:
      "h + real J * (2*eta/eps) - real (m-J) * (eta/(4*(1+eps))) < 0"
  shows "W b (n+m) < 0"
proof (rule ccontr)
  assume not_negative: "\<not> W b (n+m) < 0"
  have final: "0 \<le> W b (n+m)" using not_negative by linarith
  have start: "0 \<le> W b n"
    by (rule conjunct1[OF aw_anchor_prefix[OF anchor]])
  have nn: "\<forall>j\<le>m. 0 \<le> W b (n+j)"
    by (rule aw_tail_all_nonnegative[OF start tail final])
  have quarter: "1/4 \<le> M b (n+j)" if "J \<le> j" "j \<le> m" for j
  proof -
    have low: "1/2 - (3/2)*beta1^j \<le> M b (n+j)"
      by (rule aw_tail_moment_lower) (use tail nn that in auto)
    have power: "beta1^j \<le> beta1^J"
      by (rule aw_power_antimono) (use beta1_nonneg beta1_lt that in auto)
    show ?thesis using low power burn_momentum by linarith
  qed
  have desc: "W b (n+J+Suc i) \<le>
      W b (n+J+i) - eta/(4*(1+eps))" if "i < m-J" for i
  proof -
    have ji: "J+i < m" using burn_length that by arith
    have w0: "0 \<le> W b (n+J+i)" using nn ji by (simp add: add.assoc)
    have mq: "1/4 \<le> M b (Suc (n+J+i))"
      using quarter[of "Suc (J+i)"] ji by (simp add: add.assoc)
    show ?thesis using aw_tail_quarter_descent[OF w0 mq] by simp
  qed
  have total: "W b (n+m) \<le> W b (n+J) - real (m-J)*(eta/(4*(1+eps)))"
  proof -
    have raw: "W b (n+J+(m-J)) \<le>
        W b (n+J+0) + real (m-J)*(-eta/(4*(1+eps)))"
    proof (rule aw_affine_iteration_upper[where n="m-J" and
        f="\<lambda>i. W b (n+J+i)" and d="-eta/(4*(1+eps))"])
      fix i
      assume "i < m-J"
      then show "W b (n + J + Suc i) \<le>
          W b (n + J + i) + - eta / (4 * (1 + eps))"
        using desc[of i] by linarith
    qed
    show ?thesis using raw burn_length by (simp add: algebra_simps)
  qed
  have burn: "W b (n+J) \<le> h + real J*(2*eta/eps)"
    using aw_prefix_weight_upper[of b n J] anchor_bound by linarith
  show False using total burn takeover final by linarith
qed

corollary aw_attack_metrics:
  assumes "\<And>i. i < n \<Longrightarrow> b i"
    "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    "W b n \<le> h" "J \<le> m" "beta1^J \<le> 1/6"
    "h + real J*(2*eta/eps) - real (m-J)*(eta/(4*(1+eps))) < 0"
  shows "clean_test_risk p (W b (n+m)) = 1-p"
    and "clean_test_auc p (W b (n+m)) = p"
proof -
  have negative: "W b (n+m) < 0"
    by (rule aw_anchor_tail_inversion[OF assms])
  show "clean_test_risk p (W b (n+m)) = 1-p"
    by (rule clean_test_risk_negative[OF negative])
  show "clean_test_auc p (W b (n+m)) = p"
    by (rule clean_test_auc_negative[OF negative])
qed

end

section \<open>Deterministic interval-barrier certificate for random order\<close>

text \<open>
  This standalone theorem separates the scalar interval-barrier argument from
  optimizer dynamics. It can be instantiated whenever a trajectory supplies
  the stated bounded-jump and interval-drift certificates.
\<close>

theorem aw_interval_barrier:
  fixes w :: "nat \<Rightarrow> real"
  assumes Npos: "0 < N"
    and initial: "w 0 = 0"
    and A0: "0 \<le> A" and B0: "0 \<le> B"
    and jump: "\<And>i. i < N \<Longrightarrow> abs (w (Suc i)-w i) \<le> S"
    and interval:
      "\<And>u v. u < v \<Longrightarrow> v \<le> N \<Longrightarrow>
        (\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> w i \<le> r) \<Longrightarrow>
        A * real (v-u) - B \<le> w v - w u"
  shows "min (r-S-B) (A * real N-B) \<le> w N"
proof (cases "\<forall>i<N. w i \<le> r")
  case True
  have drift: "A * real (N-0)-B \<le> w N-w 0"
    by (rule interval[of 0 N]) (use Npos True in auto)
  have "A * real N-B \<le> w N"
    using drift initial by simp
  then show ?thesis by linarith
next
  case False
  let ?H = "{i \<in> {..<N}. r < w i}"
  have finiteH: "finite ?H" by simp
  have nonempty: "?H \<noteq> {}" using False by auto
  define k where "k = Max ?H"
  have member: "k \<in> ?H" unfolding k_def by (rule Max_in[OF finiteH nonempty])
  have kN: "k < N" and wk: "r < w k" using member by auto
  have tail: "w i \<le> r" if "Suc k \<le> i" "i < N" for i
  proof (rule ccontr)
    assume "\<not> w i \<le> r"
    then have iH: "i \<in> ?H" using that by auto
    have "i \<le> k" unfolding k_def by (rule Max_ge[OF finiteH iH])
    then show False using that by arith
  qed
  have landing: "r-S \<le> w (Suc k)"
    using jump[OF kN] wk by (simp add: abs_le_iff)
  have lower: "r-S-B \<le> w N"
  proof (cases "Suc k = N")
    case True
    have landing_N: "r-S \<le> w N" using landing True by simp
    show ?thesis using landing_N B0 by linarith
  next
    case False
    have skN: "Suc k < N" using kN False by arith
    have drift: "A * real (N-Suc k)-B \<le> w N-w (Suc k)"
      by (rule interval[OF skN order_refl]) (use tail in auto)
    have nonneg: "0 \<le> A * real (N-Suc k)"
      by (rule mult_nonneg_nonneg[OF A0]) simp
    show ?thesis using drift landing nonneg by linarith
  qed
  show ?thesis using lower by linarith
qed

corollary aw_interval_barrier_positive:
  fixes w :: "nat \<Rightarrow> real"
  assumes "0 < N" "w 0 = 0" "0 \<le> A" "0 \<le> B"
    "\<And>i. i < N \<Longrightarrow> abs (w (Suc i)-w i) \<le> S"
    "\<And>u v. u < v \<Longrightarrow> v \<le> N \<Longrightarrow>
      (\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> w i \<le> r) \<Longrightarrow>
      A * real (v-u)-B \<le> w v-w u"
    "0 < r-S-B" "0 < A * real N-B"
  shows "0 < w N"
proof -
  have lower: "min (r-S-B) (A * real N-B) \<le> w N"
    by (rule aw_interval_barrier[OF assms(1-6)])
  have positive_minimum: "0 < min (r-S-B) (A * real N-B)"
    using assms(7,8) by simp
  show ?thesis using lower positive_minimum by linarith
qed

end
