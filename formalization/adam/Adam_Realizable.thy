theory Adam_Realizable
  imports Adam_Bridge
begin

declare aw_zero_def [simp]

section \<open>Two-coordinate realizable Adam and AdamW\<close>

text \<open>
  Adam is applied coordinate-wise to the original parameters (a, theta2) of the
  linearly realizable two-coordinate model, not to the reparametrized product
  u = kappa * theta2. Each coordinate carries its own first and second moment
  with the shared global clock and the shared decoupled weight decay.
\<close>

definition aw_gstep ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   nat \<Rightarrow> real \<Rightarrow> aw_state \<Rightarrow> aw_state" where
  "aw_gstep eta beta1 beta2 eps decay t g z =
    (let m = beta1 * aw_first z + (1 - beta1) * g;
         v = beta2 * aw_second z + (1 - beta2) * g^2;
         mh = m / (1 - beta1^t);
         vh = v / (1 - beta2^t)
     in \<lparr>aw_weight = (1 - eta * decay) * aw_weight z -
                        eta * mh / (sqrt vh + eps),
            aw_first = m, aw_second = v\<rparr>)"

lemma aw_step_eq_gstep:
  "aw_step eta beta1 beta2 eps decay t b z =
    aw_gstep eta beta1 beta2 eps decay t
      (sigmoid (aw_weight z) - bool_value b) z"
  by (simp add: aw_step_def aw_gstep_def Let_def)

primrec rz_run ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> aw_state \<times> aw_state" where
  "rz_run eta beta1 beta2 eps decay kappa b 0 = (aw_zero, aw_zero)"
| "rz_run eta beta1 beta2 eps decay kappa b (Suc k) =
     (let z = rz_run eta beta1 beta2 eps decay kappa b k;
          s = signed_bool (b k);
          margin = s * aw_weight (fst z) + kappa * aw_weight (snd z)
      in (aw_gstep eta beta1 beta2 eps decay (Suc k)
            (- s * sigmoid (- margin)) (fst z),
          aw_gstep eta beta1 beta2 eps decay (Suc k)
            (- kappa * sigmoid (- margin)) (snd z)))"

locale rz_parameters = aw_parameters +
  fixes kappa :: real
  assumes kappa_pos: "0 < kappa"
begin

abbreviation RZ where "RZ b k \<equiv> rz_run eta beta1 beta2 eps decay kappa b k"
abbreviation A where "A b k \<equiv> aw_weight (fst (RZ b k))"
abbreviation T2 where "T2 b k \<equiv> aw_weight (snd (RZ b k))"
abbreviation Uc where "Uc b k \<equiv> kappa * T2 b k"
abbreviation Sg where "Sg b k \<equiv> signed_bool (b k)"
abbreviation Mrg where
  "Mrg b k \<equiv> Sg b k * A b k + Uc b k"
abbreviation Ga where "Ga b k \<equiv> - Sg b k * sigmoid (- Mrg b k)"
abbreviation G2 where "G2 b k \<equiv> - kappa * sigmoid (- Mrg b k)"
abbreviation Ma where "Ma b k \<equiv> aw_first (fst (RZ b k))"
abbreviation M2 where "M2 b k \<equiv> aw_first (snd (RZ b k))"
abbreviation Va where "Va b k \<equiv> aw_second (fst (RZ b k))"
abbreviation V2 where "V2 b k \<equiv> aw_second (snd (RZ b k))"
abbreviation MHa where "MHa b k \<equiv> Ma b k / (1-beta1^k)"
abbreviation MH2 where "MH2 b k \<equiv> M2 b k / (1-beta1^k)"
abbreviation Da where "Da b k \<equiv> sqrt (Va b k / (1-beta2^k)) + eps"
abbreviation D2 where "D2 b k \<equiv> sqrt (V2 b k / (1-beta2^k)) + eps"

lemma rz_initial [simp]:
  "A b 0 = 0" "T2 b 0 = 0" "Ma b 0 = 0" "M2 b 0 = 0"
  "Va b 0 = 0" "V2 b 0 = 0"
  by simp_all

lemma rz_a_rec [simp]:
  "A b (Suc k) = (1 - eta*decay) * A b k - eta * MHa b (Suc k) / Da b (Suc k)"
  and rz_ma_rec [simp]: "Ma b (Suc k) = beta1 * Ma b k + (1-beta1) * Ga b k"
  and rz_va_rec [simp]: "Va b (Suc k) = beta2 * Va b k + (1-beta2) * (Ga b k)^2"
  by (simp_all add: aw_gstep_def Let_def)

lemma rz_t2_rec [simp]:
  "T2 b (Suc k) = (1 - eta*decay) * T2 b k - eta * MH2 b (Suc k) / D2 b (Suc k)"
  and rz_m2_rec [simp]: "M2 b (Suc k) = beta1 * M2 b k + (1-beta1) * G2 b k"
  and rz_v2_rec [simp]: "V2 b (Suc k) = beta2 * V2 b k + (1-beta2) * (G2 b k)^2"
  by (simp_all add: aw_gstep_def Let_def)

declare rz_run.simps(2) [simp del]

lemma rz_ma_ema: "Ma b k = aw_ema beta1 (Ga b) k"
  by (induction k) simp_all

lemma rz_m2_ema: "M2 b k = aw_ema beta1 (G2 b) k"
  by (induction k) simp_all

section \<open>The second coordinate stays nonnegative and grows slowly\<close>

lemma rz_g2_bounds:
  "G2 b k \<le> 0" "- kappa \<le> G2 b k" "G2 b k < 0"
proof -
  have pos: "0 < sigmoid (- Mrg b k)" by (rule sigmoid_pos)
  have le_one: "sigmoid (- Mrg b k) \<le> 1" by (rule sigmoid_le_one)
  have prod_pos: "0 < kappa * sigmoid (- Mrg b k)"
    by (rule mult_pos_pos[OF kappa_pos pos])
  have prod_le: "kappa * sigmoid (- Mrg b k) \<le> kappa * 1"
    by (rule mult_left_mono[OF le_one]) (use kappa_pos in linarith)
  have shape: "G2 b k = - (kappa * sigmoid (- Mrg b k))" by simp
  show "G2 b k \<le> 0" using shape prod_pos by linarith
  show "G2 b k < 0" using shape prod_pos by linarith
  show "- kappa \<le> G2 b k" using shape prod_le by linarith
qed

lemma rz_m2_nonpos: "M2 b k \<le> 0"
proof -
  have "aw_ema beta1 (G2 b) k \<le> aw_ema beta1 (\<lambda>i. 0) k"
    by (rule aw_ema_mono) (use beta1_nonneg beta1_lt rz_g2_bounds(1) in auto)
  then show ?thesis by (simp add: rz_m2_ema aw_ema_constant)
qed

lemma rz_m2_lower: "- kappa * (1-beta1^k) \<le> M2 b k"
proof -
  have "aw_ema beta1 (\<lambda>i. - kappa) k \<le> aw_ema beta1 (G2 b) k"
    by (rule aw_ema_mono) (use beta1_nonneg beta1_lt rz_g2_bounds(2) in auto)
  then show ?thesis by (simp add: rz_m2_ema aw_ema_constant)
qed

lemma rz_m2_negative: "M2 b (Suc k) < 0"
proof -
  have first: "beta1 * M2 b k \<le> 0"
    by (rule mult_nonneg_nonpos[OF beta1_nonneg rz_m2_nonpos])
  have second: "(1-beta1) * G2 b k < 0"
    by (rule mult_pos_neg) (use beta1_lt rz_g2_bounds(3) in auto)
  show ?thesis using first second by simp
qed

lemma rz_mh2_bounds:
  "MH2 b (Suc k) < 0" "- kappa \<le> MH2 b (Suc k)"
proof -
  have pos: "0 < 1 - beta1^(Suc k)" by (rule aw_bias_positive)
  show "MH2 b (Suc k) < 0"
    by (rule divide_neg_pos[OF rz_m2_negative pos])
  have lower: "- kappa * (1-beta1^(Suc k)) \<le> M2 b (Suc k)"
    by (rule rz_m2_lower)
  have divided: "(- kappa * (1-beta1^(Suc k))) / (1-beta1^(Suc k)) \<le>
      M2 b (Suc k) / (1-beta1^(Suc k))"
    by (rule divide_right_mono[OF lower]) (use pos in linarith)
  have cancel: "(- kappa * (1-beta1^(Suc k))) / (1-beta1^(Suc k)) = - kappa"
    using pos by simp
  show "- kappa \<le> MH2 b (Suc k)" using divided cancel by linarith
qed

lemma rz_v2_nonneg: "0 \<le> V2 b k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have first: "0 \<le> beta2 * V2 b k"
    by (rule mult_nonneg_nonneg[OF beta2_nonneg Suc.IH])
  have second: "0 \<le> (1-beta2) * (G2 b k)^2"
    by (rule mult_nonneg_nonneg) (use beta2_lt in auto)
  show ?case using first second by simp
qed

lemma rz_d2_bounds: "eps \<le> D2 b (Suc k)" "0 < D2 b (Suc k)"
proof -
  have pos: "0 < 1 - beta2^(Suc k)"
    using aw_bias_bounds[OF beta2_nonneg beta2_lt, of k] by simp
  have quotient: "0 \<le> V2 b (Suc k) / (1 - beta2^(Suc k))"
    by (rule divide_nonneg_pos[OF rz_v2_nonneg pos])
  have root: "0 \<le> sqrt (V2 b (Suc k) / (1 - beta2^(Suc k)))"
    by (rule real_sqrt_ge_zero[OF quotient])
  show "eps \<le> D2 b (Suc k)" using root by linarith
  show "0 < D2 b (Suc k)" using root eps_pos by linarith
qed

lemma rz_t2_nonneg: "0 \<le> T2 b k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have first: "0 \<le> (1 - eta*decay) * T2 b k"
    by (rule mult_nonneg_nonneg) (use decay_step Suc.IH in auto)
  have numerator: "eta * MH2 b (Suc k) \<le> 0"
    by (rule mult_nonneg_nonpos)
      (use eta_pos rz_mh2_bounds(1)[where b=b and k=k] in auto)
  have second: "eta * MH2 b (Suc k) / D2 b (Suc k) \<le> 0"
    by (rule divide_nonpos_pos[OF numerator rz_d2_bounds(2)])
  show ?case using first second by simp
qed

lemma rz_t2_positive: "0 < T2 b (Suc k)"
proof -
  have first: "0 \<le> (1 - eta*decay) * T2 b k"
    by (rule mult_nonneg_nonneg) (use decay_step rz_t2_nonneg in auto)
  have numerator: "eta * MH2 b (Suc k) < 0"
    by (rule mult_pos_neg[OF eta_pos rz_mh2_bounds(1)])
  have second: "eta * MH2 b (Suc k) / D2 b (Suc k) < 0"
    by (rule divide_neg_pos[OF numerator rz_d2_bounds(2)])
  show ?thesis using first second by simp
qed

lemma rz_t2_step_upper:
  "T2 b (Suc k) \<le> T2 b k + eta * kappa / eps"
proof -
  have decayed: "(1 - eta*decay) * T2 b k \<le> T2 b k"
  proof (rule mult_left_le_one_le[OF rz_t2_nonneg])
    show "0 \<le> 1 - eta*decay" using decay_step by simp
    show "1 - eta*decay \<le> 1" using eta_pos decay_nonneg by simp
  qed
  have scaled: "- (eta * MH2 b (Suc k)) \<le> eta * kappa"
  proof -
    have step: "eta * (- kappa) \<le> eta * MH2 b (Suc k)"
      by (rule mult_left_mono[OF rz_mh2_bounds(2)]) (use eta_pos in linarith)
    show ?thesis using step by (simp add: algebra_simps)
  qed
  have quotient: "- (eta * MH2 b (Suc k)) / D2 b (Suc k) \<le> eta * kappa / eps"
  proof -
    have step1: "- (eta * MH2 b (Suc k)) / D2 b (Suc k) \<le>
        (eta * kappa) / D2 b (Suc k)"
      by (rule divide_right_mono[OF scaled])
        (use rz_d2_bounds(2)[where b=b and k=k] in linarith)
    have step2: "(eta * kappa) / D2 b (Suc k) \<le> (eta * kappa) / eps"
    proof (rule divide_left_mono[OF rz_d2_bounds(1)])
      show "0 \<le> eta * kappa"
        by (rule mult_nonneg_nonneg) (use eta_pos kappa_pos in auto)
      show "0 < D2 b (Suc k) * eps"
        by (rule mult_pos_pos[OF rz_d2_bounds(2) eps_pos])
    qed
    show ?thesis using step1 step2 by linarith
  qed
  have negdiv: "- (eta * MH2 b (Suc k)) / D2 b (Suc k) =
      - (eta * MH2 b (Suc k) / D2 b (Suc k))"
    by simp
  show ?thesis using decayed quotient negdiv by simp
qed

lemma rz_t2_upper: "T2 b k \<le> real k * (eta * kappa / eps)"
proof -
  have iter: "T2 b k \<le> T2 b 0 + real k * (eta * kappa / eps)"
    by (rule aw_affine_iteration_upper) (use rz_t2_step_upper in simp)
  show ?thesis using iter by simp
qed

lemma rz_u_bounds:
  "0 \<le> Uc b k" "Uc b k \<le> real k * (eta * kappa^2 / eps)"
proof -
  show "0 \<le> Uc b k"
    by (rule mult_nonneg_nonneg) (use kappa_pos rz_t2_nonneg in auto)
  have scaled: "kappa * T2 b k \<le> kappa * (real k * (eta * kappa / eps))"
    by (rule mult_left_mono[OF rz_t2_upper]) (use kappa_pos in linarith)
  have regroup: "kappa * (real k * (eta * kappa / eps)) =
      real k * (eta * kappa^2 / eps)"
    by (simp add: power2_eq_square algebra_simps)
  show "Uc b k \<le> real k * (eta * kappa^2 / eps)"
    using scaled regroup by linarith
qed

lemma rz_u_positive: "0 < Uc b (Suc k)"
  by (rule mult_pos_pos[OF kappa_pos rz_t2_positive])

section \<open>First coordinate: exact gradient identity and trajectory bounds\<close>

lemma rz_ga_identity:
  "Ga b k = sigmoid (A b k + Sg b k * Uc b k) - bool_value (b k)"
proof (cases "b k")
  case True
  have neg: "sigmoid (- (A b k + Uc b k)) = 1 - sigmoid (A b k + Uc b k)"
    by (rule sigmoid_neg_identity)
  show ?thesis using True neg
    by (simp add: signed_bool_def bool_value_def)
next
  case False
  then show ?thesis
    by (simp add: signed_bool_def bool_value_def)
qed

lemma rz_ga_bound: "abs (Ga b k) \<le> 1"
proof -
  have pos: "0 < sigmoid (A b k + Sg b k * Uc b k)" by (rule sigmoid_pos)
  have le: "sigmoid (A b k + Sg b k * Uc b k) \<le> 1" by (rule sigmoid_le_one)
  have val: "bool_value (b k) = 0 \<or> bool_value (b k) = 1"
    by (simp add: bool_value_def)
  show ?thesis
    using rz_ga_identity pos le val by (auto simp: abs_le_iff)
qed

lemma rz_ga_perturbation:
  "abs (Ga b k - (sigmoid (A b k) - bool_value (b k))) \<le> Uc b k / 4"
proof -
  have shape: "Ga b k - (sigmoid (A b k) - bool_value (b k)) =
      sigmoid (A b k + Sg b k * Uc b k) - sigmoid (A b k)"
    using rz_ga_identity[where b=b and k=k] by linarith
  have eqabs: "abs (Ga b k - (sigmoid (A b k) - bool_value (b k))) =
      abs (sigmoid (A b k + Sg b k * Uc b k) - sigmoid (A b k))"
    by (rule arg_cong[where f = abs, OF shape])
  have lip: "abs (sigmoid (A b k + Sg b k * Uc b k) - sigmoid (A b k)) \<le>
      abs (Sg b k * Uc b k) / 4"
    using sigmoid_lipschitz[of "A b k + Sg b k * Uc b k" "A b k"] by simp
  have absval: "abs (Sg b k * Uc b k) = Uc b k"
    using kappa_pos rz_t2_nonneg[where b=b and k=k]
    by (simp add: signed_bool_def abs_mult)
  show ?thesis using eqabs lip absval by linarith
qed

lemma rz_va_ema: "Va b k = aw_ema beta2 (\<lambda>i. (Ga b i)^2) k"
  by (induction k) simp_all

lemma rz_ma_bound: "abs (Ma b k) \<le> 1-beta1^k"
  unfolding rz_ma_ema
  by (rule aw_ema_abs_bound)
    (use beta1_nonneg beta1_lt rz_ga_bound in auto)

lemma rz_va_bounds:
  "0 \<le> Va b k" "Va b k \<le> 1-beta2^k"
proof -
  have bounds: "0 \<le> (Ga b i)^2 \<and> (Ga b i)^2 \<le> 1" for i
  proof
    show "0 \<le> (Ga b i)^2" by simp
    have "(abs (Ga b i))^2 \<le> (1::real)^2"
      by (rule power_mono[OF rz_ga_bound abs_ge_zero])
    then show "(Ga b i)^2 \<le> 1" by simp
  qed
  have lo: "aw_ema beta2 (\<lambda>i. 0) k \<le> aw_ema beta2 (\<lambda>i. (Ga b i)^2) k"
    by (rule aw_ema_mono) (use beta2_nonneg beta2_lt bounds in auto)
  have hi: "aw_ema beta2 (\<lambda>i. (Ga b i)^2) k \<le> aw_ema beta2 (\<lambda>i. 1) k"
    by (rule aw_ema_mono) (use beta2_nonneg beta2_lt bounds in auto)
  show "0 \<le> Va b k" "Va b k \<le> 1-beta2^k"
    using lo hi by (simp_all add: rz_va_ema aw_ema_constant)
qed

lemma rz_mha_bound: "abs (MHa b (Suc k)) \<le> 1"
proof -
  have rho: "0 < 1-beta1^(Suc k)" by (rule aw_bias_positive)
  show ?thesis using rz_ma_bound[where b=b and k="Suc k"] rho
    by (simp add: divide_le_eq)
qed

lemma rz_vhat_bounds:
  "0 \<le> Va b (Suc k) / (1-beta2^(Suc k))"
  "Va b (Suc k) / (1-beta2^(Suc k)) \<le> 1"
proof -
  have rho: "0 < 1-beta2^(Suc k)"
    using aw_bias_bounds[OF beta2_nonneg beta2_lt, of k] by blast
  show "0 \<le> Va b (Suc k) / (1-beta2^(Suc k))"
    "Va b (Suc k) / (1-beta2^(Suc k)) \<le> 1"
    using rz_va_bounds[where b=b and k="Suc k"] rho
    by (simp_all add: divide_le_eq)
qed

lemma rz_da_bounds:
  "eps \<le> Da b (Suc k)" "Da b (Suc k) \<le> 1+eps"
proof -
  have lo: "0 \<le> sqrt (Va b (Suc k) / (1-beta2^(Suc k)))"
    by (rule real_sqrt_ge_zero[OF rz_vhat_bounds(1)])
  have hi: "sqrt (Va b (Suc k) / (1-beta2^(Suc k))) \<le> sqrt 1"
    by (rule real_sqrt_le_mono[OF rz_vhat_bounds(2)])
  show "eps \<le> Da b (Suc k)" "Da b (Suc k) \<le> 1+eps"
    using lo hi by simp_all
qed

lemma rz_da_positive: "0 < Da b (Suc k)"
  using rz_da_bounds(1)[where b=b and k=k] eps_pos by linarith

lemma rz_direction_bound:
  "abs (MHa b (Suc k) / Da b (Suc k)) \<le> 1/eps"
proof -
  have dp: "0 < Da b (Suc k)" by (rule rz_da_positive)
  have ratio: "1 \<le> Da b (Suc k) / eps"
    using rz_da_bounds(1)[where b=b and k=k] eps_pos
    by (simp add: le_divide_eq)
  have identity: "(1/eps) * Da b (Suc k) = Da b (Suc k) / eps"
    by algebra
  have scaled: "abs (MHa b (Suc k)) \<le> (1/eps) * Da b (Suc k)"
    using rz_mha_bound[where b=b and k=k] ratio identity by linarith
  have quotient: "abs (MHa b (Suc k)) / Da b (Suc k) \<le> 1/eps"
    using scaled dp by (simp only: divide_le_eq if_True)
  have ad: "abs (Da b (Suc k)) = Da b (Suc k)"
    by (rule abs_of_pos[OF dp])
  have rewrite: "abs (MHa b (Suc k) / Da b (Suc k)) =
      abs (MHa b (Suc k)) / Da b (Suc k)"
  proof -
    have "abs (MHa b (Suc k) / Da b (Suc k)) =
        abs (MHa b (Suc k)) / abs (Da b (Suc k))"
      by (rule abs_divide)
    then show ?thesis by (simp only: ad)
  qed
  show ?thesis using rewrite quotient by linarith
qed

lemma rz_decay_weight_bound: "decay * abs (A b k) \<le> 1/eps"
proof (induction k)
  case 0
  then show ?case using eps_pos by simp
next
  case (Suc k)
  let ?q = "1-eta*decay"
  let ?u = "MHa b (Suc k) / Da b (Suc k)"
  have q0: "0 \<le> ?q" using decay_step by linarith
  have e0: "0 \<le> eta" using eta_pos by linarith
  have ub: "abs ?u \<le> 1/eps" by (rule rz_direction_bound)
  have rec: "A b (Suc k) = ?q * A b k - eta * ?u"
    by (simp only: rz_a_rec field_class.field_divide_inverse mult.assoc)
  have tri: "abs (A b (Suc k)) \<le> ?q * abs (A b k) + eta * abs ?u"
    using rec abs_triangle_ineq[of "?q * A b k" "-eta * ?u"] q0 e0
    by (simp add: abs_mult)
  have scaled: "decay * abs (A b (Suc k)) \<le>
      ?q * (decay * abs (A b k)) + eta * decay * abs ?u"
    using mult_left_mono[OF tri decay_nonneg] by (simp add: algebra_simps)
  have bound1: "?q * (decay * abs (A b k)) \<le> ?q * (1/eps)"
    by (rule mult_left_mono[OF Suc.IH q0])
  have factor_nonnegative: "0 \<le> eta * decay"
    by (rule mult_nonneg_nonneg[OF e0 decay_nonneg])
  have bound2: "eta * decay * abs ?u \<le> eta * decay * (1/eps)"
    by (rule mult_left_mono[OF ub factor_nonnegative])
  have identity: "?q * (1/eps) + eta * decay * (1/eps) = 1/eps"
    by algebra
  show ?case using scaled bound1 bound2 identity by linarith
qed

lemma rz_jump_bound: "abs (A b (Suc k) - A b k) \<le> 2*eta/eps"
proof -
  let ?u = "MHa b (Suc k) / Da b (Suc k)"
  have e0: "0 \<le> eta" using eta_pos by linarith
  have rec: "A b (Suc k) = (1-eta*decay) * A b k - eta * ?u"
    by (simp only: rz_a_rec field_class.field_divide_inverse mult.assoc)
  have identity: "A b (Suc k) - A b k = -eta * (decay * A b k) - eta * ?u"
    by (simp only: rec; algebra)
  have tri: "abs (A b (Suc k) - A b k) \<le>
      eta * (decay * abs (A b k)) + eta * abs ?u"
    using identity
      abs_triangle_ineq[of "-eta * (decay * A b k)" "-eta * ?u"]
      e0 decay_nonneg
    by (simp add: abs_mult del: rz_a_rec rz_ma_rec rz_va_rec)
  have a: "eta * (decay * abs (A b k)) \<le> eta * (1/eps)"
    by (rule mult_left_mono[OF rz_decay_weight_bound[where b=b and k=k] e0])
  have c: "eta * abs ?u \<le> eta * (1/eps)"
    by (rule mult_left_mono[OF rz_direction_bound[where b=b and k=k] e0])
  have final_identity: "eta * (1/eps) + eta * (1/eps) = 2*eta/eps"
    by algebra
  show ?thesis using tri a c final_identity by linarith
qed

section \<open>Tracking of the corrected first moment with the coupling slack\<close>

abbreviation Aema where
  "Aema b k \<equiv> aw_ema beta1 (\<lambda>i. sigmoid (A b i)) k"
abbreviation Pert where
  "Pert b k \<equiv>
    aw_ema beta1 (\<lambda>i. Ga b i - (sigmoid (A b i) - bool_value (b i))) k"
abbreviation UB where "UB N \<equiv> real N * (eta * kappa^2 / eps)"

lemma rz_ub_nonneg: "0 \<le> UB N"
proof (rule mult_nonneg_nonneg)
  show "0 \<le> real N" by simp
  show "0 \<le> eta * kappa^2 / eps"
    using eta_pos kappa_pos eps_pos by simp
qed

lemma rz_sigma_shift:
  "abs (sigmoid (A b k) - sigmoid (A b (Suc k))) \<le> eta/(2*eps)"
proof -
  have lip: "abs (sigmoid (A b k) - sigmoid (A b (Suc k))) \<le>
      abs (A b k - A b (Suc k)) / 4"
    by (rule sigmoid_lipschitz)
  have jump: "abs (A b k - A b (Suc k)) \<le> 2*eta/eps"
    using rz_jump_bound[where b=b and k=k] by (simp add: abs_minus_commute)
  have scaled: "abs (A b k - A b (Suc k)) / 4 \<le> (2*eta/eps) / 4"
    using jump by simp
  have simplify: "(2*eta/eps) / 4 = eta/(2*eps)"
    using eps_pos by simp
  show ?thesis using lip scaled simplify by argo
qed

lemma rz_aema_track:
  "abs (Aema b (Suc k) - (1-beta1^(Suc k)) * sigmoid (A b k)) \<le>
    (1-beta1^(Suc k)) * Kslack"
proof (induction k)
  case 0
  have base: "Aema b (Suc 0) = (1-beta1) * sigmoid (A b 0)" by simp
  have nonneg: "0 \<le> (1-beta1) * Kslack"
    by (rule mult_nonneg_nonneg) (use beta1_lt aw_slack_nonneg in auto)
  show ?case using nonneg by (simp add: base)
next
  case (Suc k)
  let ?t = "1-beta1^(Suc k)"
  let ?s = "sigmoid (A b k)"
  let ?s' = "sigmoid (A b (Suc k))"
  have tpos: "0 \<le> ?t"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by simp
  have expand: "Aema b (Suc (Suc k)) = beta1 * Aema b (Suc k) + (1-beta1) * ?s'"
    by simp
  have corr: "1 - beta1^(Suc (Suc k)) = beta1 * ?t + (1-beta1)"
    by (simp add: algebra_simps)
  have diff: "Aema b (Suc (Suc k)) - (1 - beta1^(Suc (Suc k))) * ?s' =
      beta1 * ((Aema b (Suc k) - ?t * ?s) + ?t * (?s - ?s'))"
    using expand corr by (simp add: algebra_simps)
  have shift: "abs (?s - ?s') \<le> eta/(2*eps)"
    by (rule rz_sigma_shift)
  have inner: "abs ((Aema b (Suc k) - ?t * ?s) + ?t * (?s - ?s')) \<le>
      ?t * Kslack + ?t * (eta/(2*eps))"
  proof -
    have a: "abs (Aema b (Suc k) - ?t * ?s) \<le> ?t * Kslack"
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
  have scaled: "abs (Aema b (Suc (Suc k)) - (1 - beta1^(Suc (Suc k))) * ?s') \<le>
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

lemma rz_pert_bound:
  assumes kN: "k \<le> N"
  shows "abs (Pert b k) \<le> (1-beta1^k) * (UB N / 4)"
proof -
  have pointwise: "abs (Ga b i - (sigmoid (A b i) - bool_value (b i))) \<le>
      UB N / 4" if ik: "i < k" for i
  proof -
    have step: "abs (Ga b i - (sigmoid (A b i) - bool_value (b i))) \<le>
        Uc b i / 4"
      by (rule rz_ga_perturbation)
    have small: "Uc b i \<le> UB N"
    proof -
      have local_bound: "Uc b i \<le> real i * (eta * kappa^2 / eps)"
        by (rule rz_u_bounds(2))
      have monotone: "real i * (eta * kappa^2 / eps) \<le> UB N"
      proof (rule mult_right_mono)
        show "real i \<le> real N" using ik kN by simp
        show "0 \<le> eta * kappa^2 / eps"
          using eta_pos kappa_pos eps_pos by simp
      qed
      show ?thesis using local_bound monotone by linarith
    qed
    have quarter: "Uc b i / 4 \<le> UB N / 4" using small by simp
    show ?thesis using step quarter by linarith
  qed
  have quarter_nonneg: "0 \<le> UB N / 4"
    by (rule divide_nonneg_nonneg[OF rz_ub_nonneg]) simp
  have plo: "- (UB N / 4) \<le> Ga b i - (sigmoid (A b i) - bool_value (b i))"
    if ik: "i < k" for i
    using pointwise[OF ik] by (simp add: abs_le_iff)
  have phi: "Ga b i - (sigmoid (A b i) - bool_value (b i)) \<le> UB N / 4"
    if ik: "i < k" for i
    using pointwise[OF ik] by (simp add: abs_le_iff)
  have lo: "aw_ema beta1 (\<lambda>i. - (UB N / 4)) k \<le> Pert b k"
    by (rule aw_ema_mono) (use beta1_nonneg beta1_lt plo in auto)
  have hi: "Pert b k \<le> aw_ema beta1 (\<lambda>i. UB N / 4) k"
    by (rule aw_ema_mono) (use beta1_nonneg beta1_lt phi in auto)
  show ?thesis using lo hi
    by (simp add: aw_ema_constant abs_le_iff algebra_simps)
qed

lemma rz_ma_split:
  "Ma b k = (Aema b k - Bema b k) + Pert b k"
proof -
  have shape: "Ga b i = (sigmoid (A b i) - bool_value (b i)) +
      (Ga b i - (sigmoid (A b i) - bool_value (b i)))" for i
    by simp
  have split: "aw_ema beta1 (Ga b) k =
      aw_ema beta1 (\<lambda>i. sigmoid (A b i) - bool_value (b i)) k +
      aw_ema beta1 (\<lambda>i. Ga b i - (sigmoid (A b i) - bool_value (b i))) k"
    using aw_ema_add[where beta=beta1
      and x="\<lambda>i. sigmoid (A b i) - bool_value (b i)"
      and y="\<lambda>i. Ga b i - (sigmoid (A b i) - bool_value (b i))" and n=k]
    by simp
  have inner: "aw_ema beta1 (\<lambda>i. sigmoid (A b i) - bool_value (b i)) k =
      Aema b k - Bema b k"
    by (rule aw_ema_diff)
  show ?thesis using rz_ma_ema split inner by simp
qed

lemma rz_moment_track:
  assumes kN: "k < N"
  shows "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) \<le>
    Kslack + UB N / 4"
proof -
  let ?t = "1-beta1^(Suc k)"
  have pos: "0 < ?t" by (rule aw_bias_positive)
  have tne: "?t \<noteq> 0" using pos by simp
  have split: "Ma b (Suc k) = (Aema b (Suc k) - Bema b (Suc k)) + Pert b (Suc k)"
    by (rule rz_ma_split)
  have combine: "MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k)) =
      (Aema b (Suc k) + Pert b (Suc k)) / ?t - sigmoid (A b k)"
    using split by (simp add: diff_divide_distrib add_divide_distrib)
  have quotient: "(Aema b (Suc k) + Pert b (Suc k)) / ?t - sigmoid (A b k) =
      (Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) / ?t"
    using tne by (simp add: field_simps)
  have eq: "MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k)) =
      (Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) / ?t"
    by (rule trans[OF combine quotient])
  have track: "abs (Aema b (Suc k) - ?t * sigmoid (A b k)) \<le> ?t * Kslack"
    by (rule rz_aema_track)
  have pert: "abs (Pert b (Suc k)) \<le> ?t * (UB N / 4)"
    by (rule rz_pert_bound) (use kN in simp)
  have numerator:
      "abs (Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) \<le>
        ?t * Kslack + ?t * (UB N / 4)"
    using track pert by linarith
  have absval: "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) =
      abs (Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) / ?t"
  proof -
    have step: "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) =
        abs ((Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) / ?t)"
      by (rule arg_cong[where f = abs, OF eq])
    show ?thesis using step pos by simp
  qed
  have divided:
      "abs (Aema b (Suc k) - ?t * sigmoid (A b k) + Pert b (Suc k)) / ?t \<le>
        (?t * Kslack + ?t * (UB N / 4)) / ?t"
    by (rule divide_right_mono[OF numerator]) (use pos in linarith)
  have cancel: "(?t * Kslack + ?t * (UB N / 4)) / ?t = Kslack + UB N / 4"
    using tne by (simp add: field_simps)
  show ?thesis using absval divided cancel by linarith
qed

section \<open>Per-step drift of the first coordinate\<close>

abbreviation Slack where "Slack N \<equiv> Kslack + UB N / 4"

lemma rz_slack_nonneg: "0 \<le> Slack N"
proof -
  have quarter: "0 \<le> UB N / 4"
    by (rule divide_nonneg_nonneg[OF rz_ub_nonneg]) simp
  show ?thesis using aw_slack_nonneg quarter by linarith
qed

lemma rz_step_drift_lower:
  assumes wk: "A b k \<le> delta" and kN: "k < N"
  shows "eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
      eta * Slack N / eps - eta * (1 - ZH b (Suc k)) / eps \<le>
    A b (Suc k) - A b k"
proof -
  have dp: "0 < Da b (Suc k)" by (rule rz_da_positive)
  have dlow: "eps \<le> Da b (Suc k)" by (rule rz_da_bounds(1))
  have dhigh: "Da b (Suc k) \<le> 1+eps" by (rule rz_da_bounds(2))
  have track: "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) \<le> Slack N"
    by (rule rz_moment_track[OF kN])
  have upper: "MHa b (Suc k) \<le> sigmoid (A b k) - ZH b (Suc k) + Slack N"
    using track by (simp add: abs_le_iff)
  have identity: "- (sigmoid (A b k) - ZH b (Suc k) + Slack N) =
      sigmoid (- A b k) - (1 - ZH b (Suc k)) - Slack N"
    by (simp add: sigmoid_neg_identity)
  have negate: "sigmoid (- A b k) - (1 - ZH b (Suc k)) - Slack N \<le>
      - MHa b (Suc k)"
    using upper identity by argo
  have step: "eta * (sigmoid (- A b k) - (1 - ZH b (Suc k)) - Slack N) \<le>
      eta * (- MHa b (Suc k))"
    by (rule mult_left_mono[OF negate]) (use eta_pos in linarith)
  have div_mono: "eta * (sigmoid (- A b k) - (1 - ZH b (Suc k)) - Slack N) /
        Da b (Suc k) \<le> eta * (- MHa b (Suc k)) / Da b (Suc k)"
    by (rule divide_right_mono[OF step]) (use dp in linarith)
  have split: "eta * (sigmoid (- A b k) - (1 - ZH b (Suc k)) - Slack N) /
        Da b (Suc k) =
      eta * sigmoid (- A b k) / Da b (Suc k) -
      eta * (1 - ZH b (Suc k)) / Da b (Suc k) -
      eta * Slack N / Da b (Suc k)"
    by (rule real_scaled_split)
  have sig_mono: "sigmoid (-delta) \<le> sigmoid (- A b k)"
    using sigmoid_difference_bounds(1)[of "-delta" "- A b k"] wk by simp
  have num: "eta * sigmoid (-delta) \<le> eta * sigmoid (- A b k)"
    by (rule mult_left_mono[OF sig_mono]) (use eta_pos in linarith)
  have num_nonneg: "0 \<le> eta * sigmoid (-delta)"
    using sigmoid_pos[of "-delta"] eta_pos by simp
  have den: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (-delta) / Da b (Suc k)"
  proof (rule divide_left_mono[OF dhigh num_nonneg])
    show "0 < (1+eps) * Da b (Suc k)" using dp eps_pos by simp
  qed
  have num_div: "eta * sigmoid (-delta) / Da b (Suc k) \<le>
      eta * sigmoid (- A b k) / Da b (Suc k)"
    by (rule divide_right_mono[OF num]) (use dp in linarith)
  have a_low: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (- A b k) / Da b (Suc k)"
    using den num_div by linarith
  have zh_le: "ZH b (Suc k) \<le> 1" by (rule aw_zh_bounds(2))
  have b_low: "eta * (1 - ZH b (Suc k)) / Da b (Suc k) \<le>
      eta * (1 - ZH b (Suc k)) / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * (1 - ZH b (Suc k))"
      by (rule mult_nonneg_nonneg) (use zh_le eta_pos in auto)
    show "0 < Da b (Suc k) * eps" using dp eps_pos by simp
  qed
  have c_low: "eta * Slack N / Da b (Suc k) \<le> eta * Slack N / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * Slack N"
      by (rule mult_nonneg_nonneg) (use eta_pos rz_slack_nonneg in auto)
    show "0 < Da b (Suc k) * eps" using dp eps_pos by simp
  qed
  have decay_bound: "eta * decay * A b k \<le> eta * decay * delta"
    by (rule mult_left_mono[OF wk]) (use eta_pos decay_nonneg in simp)
  have expand: "(1 - eta*decay) * A b k = A b k - eta*decay*A b k"
    by (simp add: algebra_simps)
  have rec: "A b (Suc k) - A b k =
      - (eta*decay*A b k) - eta * MHa b (Suc k) / Da b (Suc k)"
    using rz_a_rec[where b=b and k=k] expand by linarith
  have negdiv: "eta * (- MHa b (Suc k)) / Da b (Suc k) =
      - (eta * MHa b (Suc k) / Da b (Suc k))"
    by simp
  show ?thesis
    using rec div_mono split a_low b_low c_low decay_bound negdiv
    by linarith
qed

lemma rz_step_drift_upper:
  assumes wk: "- delta \<le> A b k" and kN: "k < N"
  shows "A b (Suc k) - A b k \<le>
    eta * decay * delta - eta * sigmoid (-delta) / (1+eps) +
      eta * Slack N / eps + eta * ZH b (Suc k) / eps"
proof -
  have dp: "0 < Da b (Suc k)" by (rule rz_da_positive)
  have dlow: "eps \<le> Da b (Suc k)" by (rule rz_da_bounds(1))
  have dhigh: "Da b (Suc k) \<le> 1+eps" by (rule rz_da_bounds(2))
  have track: "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) \<le> Slack N"
    by (rule rz_moment_track[OF kN])
  have lower: "sigmoid (A b k) - ZH b (Suc k) - Slack N \<le> MHa b (Suc k)"
    using track by (simp add: abs_le_iff)
  have step: "eta * (sigmoid (A b k) - ZH b (Suc k) - Slack N) \<le>
      eta * MHa b (Suc k)"
    by (rule mult_left_mono[OF lower]) (use eta_pos in linarith)
  have div_mono: "eta * (sigmoid (A b k) - ZH b (Suc k) - Slack N) /
        Da b (Suc k) \<le> eta * MHa b (Suc k) / Da b (Suc k)"
    by (rule divide_right_mono[OF step]) (use dp in linarith)
  have split: "eta * (sigmoid (A b k) - ZH b (Suc k) - Slack N) / Da b (Suc k) =
      eta * sigmoid (A b k) / Da b (Suc k) -
      eta * ZH b (Suc k) / Da b (Suc k) -
      eta * Slack N / Da b (Suc k)"
    by (rule real_scaled_split)
  have sig_mono: "sigmoid (-delta) \<le> sigmoid (A b k)"
    using sigmoid_difference_bounds(1)[of "-delta" "A b k"] wk by simp
  have num: "eta * sigmoid (-delta) \<le> eta * sigmoid (A b k)"
    by (rule mult_left_mono[OF sig_mono]) (use eta_pos in linarith)
  have num_nonneg: "0 \<le> eta * sigmoid (-delta)"
    using sigmoid_pos[of "-delta"] eta_pos by simp
  have den: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (-delta) / Da b (Suc k)"
  proof (rule divide_left_mono[OF dhigh num_nonneg])
    show "0 < (1+eps) * Da b (Suc k)" using dp eps_pos by simp
  qed
  have num_div: "eta * sigmoid (-delta) / Da b (Suc k) \<le>
      eta * sigmoid (A b k) / Da b (Suc k)"
    by (rule divide_right_mono[OF num]) (use dp in linarith)
  have a_low: "eta * sigmoid (-delta) / (1+eps) \<le>
      eta * sigmoid (A b k) / Da b (Suc k)"
    using den num_div by linarith
  have zh_nonneg: "0 \<le> ZH b (Suc k)" by (rule aw_zh_bounds(1))
  have b_low: "eta * ZH b (Suc k) / Da b (Suc k) \<le> eta * ZH b (Suc k) / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * ZH b (Suc k)"
      by (rule mult_nonneg_nonneg) (use zh_nonneg eta_pos in auto)
    show "0 < Da b (Suc k) * eps" using dp eps_pos by simp
  qed
  have c_low: "eta * Slack N / Da b (Suc k) \<le> eta * Slack N / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * Slack N"
      by (rule mult_nonneg_nonneg) (use eta_pos rz_slack_nonneg in auto)
    show "0 < Da b (Suc k) * eps" using dp eps_pos by simp
  qed
  have decay_bound: "- (eta * decay * A b k) \<le> eta * decay * delta"
  proof -
    have factor: "0 \<le> eta * decay"
      by (rule mult_nonneg_nonneg) (use eta_pos decay_nonneg in auto)
    have step2: "eta * decay * (- delta) \<le> eta * decay * A b k"
      by (rule mult_left_mono[OF wk factor])
    show ?thesis using step2 by (simp add: algebra_simps)
  qed
  have expand: "(1 - eta*decay) * A b k = A b k - eta*decay*A b k"
    by (simp add: algebra_simps)
  have rec: "A b (Suc k) - A b k =
      - (eta*decay*A b k) - eta * MHa b (Suc k) / Da b (Suc k)"
    using rz_a_rec[where b=b and k=k] expand by linarith
  show ?thesis
    using rec div_mono split a_low b_low c_low decay_bound
    by linarith
qed

section \<open>Interval drift of the first coordinate\<close>

lemma rz_interval_drift_lower:
  assumes uv: "u \<le> v" and vN: "v \<le> N"
    and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> A b i \<le> delta"
    and disc: "\<And>k. k \<le> N \<Longrightarrow>
      abs ((\<Sum>i<k. bool_value (b i)) - p * real k) \<le> Dsc"
  shows "real (v-u) * (eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
        eta * Slack N / eps - eta * (1-p) / eps) -
      (eta/eps) * (2*Dsc + beta1/(1-beta1)) \<le> A b v - A b u"
proof -
  let ?C = "eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
      eta * Slack N / eps"
  let ?t = "\<lambda>i. eta * (1 - ZH b (Suc i)) / eps"
  have telescope: "(\<Sum>i=u..<v. A b (Suc i) - A b i) = A b v - A b u"
    by (rule sum_Suc_diff'[OF uv])
  have stepwise: "(\<Sum>i=u..<v. ?C - ?t i) \<le> (\<Sum>i=u..<v. A b (Suc i) - A b i)"
  proof (rule sum_mono)
    fix i
    assume i: "i \<in> {u..<v}"
    have wi: "A b i \<le> delta" using pre i by simp
    have iN: "i < N" using i vN by simp
    show "?C - ?t i \<le> A b (Suc i) - A b i"
      using rz_step_drift_lower[OF wi iN] by simp
  qed
  have split: "(\<Sum>i=u..<v. ?C - ?t i) = real (v-u) * ?C - (\<Sum>i=u..<v. ?t i)"
    by (simp add: sum_subtractf)
  have tsum: "(\<Sum>i=u..<v. ?t i) = (eta/eps) * (\<Sum>i=u..<v. (1 - ZH b (Suc i)))"
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
        eta * decay * delta - eta * Slack N / eps - eta * (1-p) / eps) =
      real (v-u) * ?C - real (v-u) * (eta * (1-p) / eps)"
    by (simp add: algebra_simps)
  show ?thesis
    using telescope stepwise split tsum scaled regroup distrib by argo
qed

lemma rz_zh_le_bema_shift:
  "ZH b (Suc k) \<le> Bema b (Suc k) / (1-beta1)"
proof -
  have pos: "0 < 1 - beta1^(Suc k)" by (rule aw_bias_positive)
  have beta_pos: "0 < 1 - beta1" using beta1_lt by simp
  have power: "beta1^(Suc k) \<le> beta1"
  proof -
    have base: "beta1^k \<le> 1"
      using aw_power_bounds[OF beta1_nonneg, of k] beta1_lt by simp
    have step: "beta1 * beta1^k \<le> beta1 * 1"
      by (rule mult_left_mono[OF base beta1_nonneg])
    show ?thesis using step by simp
  qed
  have order: "1 - beta1 \<le> 1 - beta1^(Suc k)" using power by simp
  show ?thesis
  proof (rule divide_left_mono[OF order])
    show "0 \<le> Bema b (Suc k)" by (rule aw_bema_bounds(1))
    show "0 < (1 - beta1^(Suc k)) * (1 - beta1)"
      by (rule mult_pos_pos[OF pos beta_pos])
  qed
qed

lemma rz_tail_zh_sum:
  assumes uv: "u \<le> v"
    and tail: "\<And>j. u \<le> j \<Longrightarrow> j < v \<Longrightarrow> \<not> b j"
  shows "(\<Sum>i=u..<v. ZH b (Suc i)) \<le> beta1 / ((1-beta1) * (1-beta1))"
proof -
  have beta_pos: "0 < 1 - beta1" using beta1_lt by simp
  have telescope: "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
      beta1 * (Bema b u - Bema b v) / (1-beta1)"
    by (rule aw_bema_interval_sum[OF uv])
  have zeros: "(\<Sum>i=u..<v. Bema b (Suc i) - bool_value (b i)) =
      (\<Sum>i=u..<v. Bema b (Suc i))"
    by (rule sum.cong) (use tail bool_value_def in auto)
  have gap: "Bema b u - Bema b v \<le> 1"
  proof -
    have hi: "Bema b u \<le> 1 - beta1^u" by (rule aw_bema_bounds(2))
    have power: "0 \<le> beta1^u"
      using aw_power_bounds[OF beta1_nonneg, of u] beta1_lt by simp
    have lo: "0 \<le> Bema b v" by (rule aw_bema_bounds(1))
    show ?thesis using hi power lo by linarith
  qed
  have scaled: "beta1 * (Bema b u - Bema b v) \<le> beta1 * 1"
    by (rule mult_left_mono[OF gap beta1_nonneg])
  have divided: "beta1 * (Bema b u - Bema b v) / (1-beta1) \<le> beta1 / (1-beta1)"
    using scaled beta_pos by (simp add: divide_right_mono)
  have bema_sum: "(\<Sum>i=u..<v. Bema b (Suc i)) \<le> beta1 / (1-beta1)"
    using telescope zeros divided by linarith
  have pointwise: "(\<Sum>i=u..<v. ZH b (Suc i)) \<le>
      (\<Sum>i=u..<v. Bema b (Suc i) / (1-beta1))"
    by (rule sum_mono) (use rz_zh_le_bema_shift in simp)
  have factored: "(\<Sum>i=u..<v. Bema b (Suc i) / (1-beta1)) =
      (\<Sum>i=u..<v. Bema b (Suc i)) / (1-beta1)"
    by (simp add: sum_divide_distrib)
  have final: "(\<Sum>i=u..<v. Bema b (Suc i)) / (1-beta1) \<le>
      (beta1 / (1-beta1)) / (1-beta1)"
    by (rule divide_right_mono[OF bema_sum]) (use beta_pos in linarith)
  have shape: "(beta1 / (1-beta1)) / (1-beta1) =
      beta1 / ((1-beta1) * (1-beta1))"
    by simp
  show ?thesis using pointwise factored final shape by linarith
qed

lemma rz_interval_drift_upper:
  assumes uv: "u \<le> v" and vN: "v \<le> N"
    and tail: "\<And>j. u \<le> j \<Longrightarrow> j < v \<Longrightarrow> \<not> b j"
    and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> - delta \<le> A b i"
  shows "A b v - A b u \<le>
    real (v-u) * (eta * decay * delta - eta * sigmoid (-delta) / (1+eps) +
      eta * Slack N / eps) +
    (eta/eps) * (beta1 / ((1-beta1) * (1-beta1)))"
proof -
  let ?C = "eta * decay * delta - eta * sigmoid (-delta) / (1+eps) +
      eta * Slack N / eps"
  let ?t = "\<lambda>i. eta * ZH b (Suc i) / eps"
  have telescope: "(\<Sum>i=u..<v. A b (Suc i) - A b i) = A b v - A b u"
    by (rule sum_Suc_diff'[OF uv])
  have stepwise: "(\<Sum>i=u..<v. A b (Suc i) - A b i) \<le> (\<Sum>i=u..<v. ?C + ?t i)"
  proof (rule sum_mono)
    fix i
    assume i: "i \<in> {u..<v}"
    have wi: "- delta \<le> A b i" using pre i by simp
    have iN: "i < N" using i vN by simp
    show "A b (Suc i) - A b i \<le> ?C + ?t i"
      using rz_step_drift_upper[OF wi iN] by simp
  qed
  have split: "(\<Sum>i=u..<v. ?C + ?t i) = real (v-u) * ?C + (\<Sum>i=u..<v. ?t i)"
    by (simp add: sum.distrib)
  have tsum: "(\<Sum>i=u..<v. ?t i) = (eta/eps) * (\<Sum>i=u..<v. ZH b (Suc i))"
  proof -
    have pt: "(\<Sum>i=u..<v. ?t i) = (\<Sum>i=u..<v. (eta/eps) * ZH b (Suc i))"
      by (rule sum.cong) auto
    show ?thesis using pt by (simp add: sum_distrib_left)
  qed
  have zh_sum: "(\<Sum>i=u..<v. ZH b (Suc i)) \<le> beta1 / ((1-beta1) * (1-beta1))"
    by (rule rz_tail_zh_sum[OF uv]) (use tail in simp)
  have scale_nonneg: "0 \<le> eta/eps" using eta_pos eps_pos by simp
  have scaled: "(eta/eps) * (\<Sum>i=u..<v. ZH b (Suc i)) \<le>
      (eta/eps) * (beta1 / ((1-beta1) * (1-beta1)))"
    by (rule mult_left_mono[OF zh_sum scale_nonneg])
  show ?thesis using telescope stepwise split tsum scaled by argo
qed

section \<open>Explicit Anchor bound for the first coordinate\<close>

lemma rz_anchor_prefix:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
  shows "0 \<le> A b n \<and> Ma b n \<le> 0"
  using anchor
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have ih: "0 \<le> A b n \<and> Ma b n \<le> 0"
    by (rule Suc.IH) (use Suc.prems in simp)
  have anchor_n: "b n" using Suc.prems by simp
  have gneg: "Ga b n \<le> 0"
  proof -
    have le: "sigmoid (A b n + Sg b n * Uc b n) \<le> 1" by (rule sigmoid_le_one)
    have val: "bool_value (b n) = 1" using anchor_n by (simp add: bool_value_def)
    show ?thesis using rz_ga_identity[where b=b and k=n] le val by linarith
  qed
  have mneg: "Ma b (Suc n) \<le> 0"
  proof -
    have first: "beta1 * Ma b n \<le> 0"
      by (rule mult_nonneg_nonpos[OF beta1_nonneg]) (use ih in simp)
    have second: "(1-beta1) * Ga b n \<le> 0"
      by (rule mult_nonneg_nonpos) (use beta1_lt gneg in auto)
    show ?thesis using first second by simp
  qed
  have mhneg: "MHa b (Suc n) \<le> 0"
    using mneg aw_bias_positive[of n] by (simp add: divide_nonpos_pos)
  have wnonneg: "0 \<le> A b (Suc n)"
  proof -
    have first: "0 \<le> (1 - eta*decay) * A b n"
      by (rule mult_nonneg_nonneg) (use decay_step ih in auto)
    have numerator: "eta * MHa b (Suc n) \<le> 0"
      by (rule mult_nonneg_nonpos) (use eta_pos mhneg in auto)
    have second: "eta * MHa b (Suc n) / Da b (Suc n) \<le> 0"
      by (rule divide_nonpos_pos[OF numerator rz_da_positive])
    show ?thesis using first second by simp
  qed
  show ?case using wnonneg mneg by simp
qed

lemma rz_anchor_zh:
  assumes anchor: "\<And>i. i < Suc k \<Longrightarrow> b i"
  shows "ZH b (Suc k) = 1"
proof -
  have bema: "Bema b (Suc k) = aw_ema beta1 (\<lambda>i. 1) (Suc k)"
    by (rule aw_ema_cong) (use anchor bool_value_def in auto)
  have const_ema: "aw_ema beta1 (\<lambda>i. (1::real)) (Suc k) = 1 - beta1^(Suc k)"
    by (simp add: aw_ema_constant)
  have total: "Bema b (Suc k) = 1 - beta1^(Suc k)"
    by (rule trans[OF bema const_ema])
  have ratio: "(1 - beta1^(Suc k)) / (1 - beta1^(Suc k)) = 1"
    using aw_bias_positive[of k] by simp
  show ?thesis unfolding total by (rule ratio)
qed

lemma rz_anchor_weight_step:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and kn: "k < n" and kN: "k < N"
  shows "A b (Suc k) \<le> anchor_step alpha (A b k) + alpha * Slack N"
proof -
  have wk: "0 \<le> A b k"
  proof -
    have pair: "0 \<le> A b k \<and> Ma b k \<le> 0"
      by (rule rz_anchor_prefix) (use anchor kn in auto)
    show ?thesis using pair by simp
  qed
  have dp: "0 < Da b (Suc k)" by (rule rz_da_positive)
  have dlow: "eps \<le> Da b (Suc k)" by (rule rz_da_bounds(1))
  have zh: "ZH b (Suc k) = 1"
    by (rule rz_anchor_zh) (use anchor kn in auto)
  have lower: "- sigmoid (- A b k) - Slack N \<le> MHa b (Suc k)"
  proof -
    have track: "abs (MHa b (Suc k) - (sigmoid (A b k) - ZH b (Suc k))) \<le>
        Slack N"
      by (rule rz_moment_track[OF kN])
    have neg: "sigmoid (A b k) - 1 = - sigmoid (- A b k)"
      by (simp add: sigmoid_neg_identity)
    show ?thesis using track zh neg by (simp add: abs_le_iff)
  qed
  have num_nonneg: "0 \<le> sigmoid (- A b k) + Slack N"
    using sigmoid_pos[of "- A b k"] rz_slack_nonneg[of N] by linarith
  have scaled0: "eta * (- sigmoid (- A b k) - Slack N) \<le> eta * MHa b (Suc k)"
    by (rule mult_left_mono[OF lower]) (use eta_pos in linarith)
  have dist: "eta * (- sigmoid (- A b k) - Slack N) =
      - (eta * (sigmoid (- A b k) + Slack N))"
    by (simp add: algebra_simps)
  have scaled: "- (eta * MHa b (Suc k)) \<le> eta * (sigmoid (- A b k) + Slack N)"
    using scaled0 dist by linarith
  have step1: "(- (eta * MHa b (Suc k))) / Da b (Suc k) \<le>
      (eta * (sigmoid (- A b k) + Slack N)) / Da b (Suc k)"
    by (rule divide_right_mono[OF scaled]) (use dp in linarith)
  have step2: "(eta * (sigmoid (- A b k) + Slack N)) / Da b (Suc k) \<le>
      (eta * (sigmoid (- A b k) + Slack N)) / eps"
  proof (rule divide_left_mono[OF dlow])
    show "0 \<le> eta * (sigmoid (- A b k) + Slack N)"
      by (rule mult_nonneg_nonneg) (use num_nonneg eta_pos in auto)
    show "0 < Da b (Suc k) * eps" using dp eps_pos by simp
  qed
  have quotient: "(- (eta * MHa b (Suc k))) / Da b (Suc k) \<le>
      (eta * (sigmoid (- A b k) + Slack N)) / eps"
    using step1 step2 by linarith
  have negdiv: "(- (eta * MHa b (Suc k))) / Da b (Suc k) =
      - (eta * MHa b (Suc k) / Da b (Suc k))"
    by simp
  have decayed: "(1 - eta*decay) * A b k \<le> A b k"
  proof (rule mult_left_le_one_le[OF wk])
    show "0 \<le> 1 - eta*decay" using decay_step by simp
    show "1 - eta*decay \<le> 1" using eta_pos decay_nonneg by simp
  qed
  have combine: "A b (Suc k) \<le> A b k +
      (eta * (sigmoid (- A b k) + Slack N)) / eps"
    using rz_a_rec[where b=b and k=k] decayed quotient negdiv by linarith
  have expand: "(eta * (sigmoid (- A b k) + Slack N)) / eps =
      alpha * sigmoid (- A b k) + alpha * Slack N"
    by (simp add: algebra_simps add_divide_distrib)
  show ?thesis unfolding anchor_step_def using combine expand by linarith
qed

lemma rz_anchor_weight_le:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and alpha_le: "alpha \<le> 4"
    and nN: "n \<le> N" and jn: "j \<le> n"
  shows "A b j \<le> anchor_state alpha j + real j * (alpha * Slack N)"
  using jn
proof (induction j)
  case 0
  show ?case by (simp add: anchor_state_def)
next
  case (Suc j)
  have alpha_nonneg: "0 \<le> alpha" using eta_pos eps_pos by simp
  have product: "0 \<le> alpha * Slack N"
    by (rule mult_nonneg_nonneg[OF alpha_nonneg rz_slack_nonneg])
  have slack_nonneg: "0 \<le> real j * (alpha * Slack N)"
    by (rule mult_nonneg_nonneg) (use product in auto)
  have ih: "A b j \<le> anchor_state alpha j + real j * (alpha * Slack N)"
    by (rule Suc.IH) (use Suc.prems in simp)
  have jn': "j < n" using Suc.prems by arith
  have jN: "j < N" using jn' nN by arith
  have step: "A b (Suc j) \<le> anchor_step alpha (A b j) + alpha * Slack N"
    by (rule rz_anchor_weight_step[OF anchor jn' jN])
  have mono: "anchor_step alpha (A b j) \<le>
      anchor_step alpha (anchor_state alpha j + real j * (alpha * Slack N))"
    by (rule anchor_step_mono[OF alpha_nonneg alpha_le ih])
  have shift: "anchor_step alpha (anchor_state alpha j +
        real j * (alpha * Slack N)) \<le>
      anchor_step alpha (anchor_state alpha j) + real j * (alpha * Slack N)"
    by (rule anchor_step_shift[OF alpha_nonneg slack_nonneg])
  have unfold: "anchor_step alpha (anchor_state alpha j) =
      anchor_state alpha (Suc j)"
    by (simp add: anchor_state_Suc)
  have chain: "A b (Suc j) \<le> anchor_state alpha (Suc j) +
      real j * (alpha * Slack N) + alpha * Slack N"
    using step mono shift unfold by linarith
  have count: "real (Suc j) * (alpha * Slack N) =
      real j * (alpha * Slack N) + alpha * Slack N"
    by (simp add: algebra_simps add_divide_distrib)
  show ?case using chain count by linarith
qed

theorem rz_anchor_log_bound:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i" and alpha_le: "alpha \<le> 4"
    and nN: "n \<le> N"
  shows "A b n \<le> ln (1 + real n * (exp alpha - 1)) + real n * (alpha * Slack N)"
proof -
  have alpha_nonneg: "0 \<le> alpha" using eta_pos eps_pos by simp
  have compare: "A b n \<le> anchor_state alpha n + real n * (alpha * Slack N)"
    by (rule rz_anchor_weight_le[OF anchor alpha_le nN order_refl])
  have logarithmic: "anchor_state alpha n \<le> ln (1 + real n * (exp alpha - 1))"
    by (rule anchor_log_bound[OF alpha_nonneg])
  show ?thesis using compare logarithmic by linarith
qed

section \<open>Tail sign persistence\<close>

lemma rz_tail_gradient_positive:
  assumes tail: "\<not> b k"
  shows "0 < Ga b k"
proof -
  have shape: "Ga b k = sigmoid (A b k - Uc b k)"
    using tail by (simp add: signed_bool_def)
  show ?thesis unfolding shape by (rule sigmoid_pos)
qed

lemma rz_tail_gradient_floor:
  assumes tail: "\<not> b k" and anonneg: "0 \<le> A b k" and usmall: "Uc b k \<le> 1"
  shows "sigmoid (-1) \<le> Ga b k"
proof -
  have input: "-1 \<le> A b k - Uc b k" using anonneg usmall by linarith
  have mono: "0 \<le> sigmoid (A b k - Uc b k) - sigmoid (-1)"
    by (rule sigmoid_difference_bounds(1)[OF input])
  have shape: "Ga b k = sigmoid (A b k - Uc b k)"
    using tail by (simp add: signed_bool_def)
  show ?thesis using mono shape by linarith
qed

lemma rz_tail_negative_step:
  assumes tail: "\<not> b k" and aneg: "A b k < 0" and mnonneg: "0 \<le> Ma b k"
  shows "A b (Suc k) < 0 \<and> 0 < Ma b (Suc k)"
proof -
  have gpos: "0 < Ga b k"
    by (rule rz_tail_gradient_positive[where b=b and k=k, OF tail])
  have first: "0 \<le> beta1 * Ma b k"
    by (rule mult_nonneg_nonneg[OF beta1_nonneg mnonneg])
  have second: "0 < (1-beta1) * Ga b k"
    by (rule mult_pos_pos) (use beta1_lt gpos in auto)
  have mpos: "0 < Ma b (Suc k)" using first second by simp
  have mhpos: "0 < MHa b (Suc k)"
    by (rule divide_pos_pos[OF mpos aw_bias_positive])
  have decayed: "(1-eta*decay) * A b k \<le> 0"
    by (rule mult_nonneg_nonpos) (use decay_step aneg in auto)
  have numerator_pos: "0 < eta * MHa b (Suc k)"
    by (rule mult_pos_pos[OF eta_pos mhpos])
  have update_pos: "0 < eta * MHa b (Suc k) / Da b (Suc k)"
    by (rule divide_pos_pos[OF numerator_pos rz_da_positive])
  have anew: "A b (Suc k) < 0" using decayed update_pos by simp
  show ?thesis using anew mpos by simp
qed

lemma rz_crossing_positive_moment:
  assumes anonneg: "0 \<le> A b k" and next_negative: "A b (Suc k) < 0"
  shows "0 < Ma b (Suc k)"
proof (rule ccontr)
  assume not_positive: "\<not> 0 < Ma b (Suc k)"
  have mnonpos: "Ma b (Suc k) \<le> 0" using not_positive by simp
  have mhnonpos: "MHa b (Suc k) \<le> 0"
    by (rule divide_nonpos_pos[OF mnonpos aw_bias_positive])
  have decayed: "0 \<le> (1-eta*decay) * A b k"
    by (rule mult_nonneg_nonneg) (use decay_step anonneg in auto)
  have numerator_nonpos: "eta * MHa b (Suc k) \<le> 0"
    by (rule mult_nonneg_nonpos) (use eta_pos mhnonpos in auto)
  have update_nonpos: "eta * MHa b (Suc k) / Da b (Suc k) \<le> 0"
    by (rule divide_nonpos_pos[OF numerator_nonpos rz_da_positive])
  have "0 \<le> A b (Suc k)" using decayed update_nonpos by simp
  then show False using next_negative by simp
qed

lemma rz_tail_negative_has_positive_moment:
  assumes tail: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)"
    and start_nonnegative: "0 \<le> A b n"
    and final_negative: "A b (n+j) < 0"
  shows "0 < Ma b (n+j)"
  using tail final_negative
proof (induction j)
  case 0
  then show ?case using start_nonnegative by simp
next
  case (Suc j)
  have tail_prefix: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)"
    using Suc.prems(1) by simp
  have tail_last: "\<not> b (n+j)" using Suc.prems(1) by simp
  have final_suc: "A b (Suc (n+j)) < 0" using Suc.prems(2) by simp
  show ?case
  proof (cases "A b (n+j) < 0")
    case True
    have mpos: "0 < Ma b (n+j)" by (rule Suc.IH[OF tail_prefix True])
    have step: "A b (Suc (n+j)) < 0 \<and> 0 < Ma b (Suc (n+j))"
      by (rule rz_tail_negative_step[where b=b and k="n+j", OF tail_last True])
        (use mpos in auto)
    show ?thesis using step by simp
  next
    case False
    have anonneg: "0 \<le> A b (n+j)" using False by simp
    have mpos: "0 < Ma b (Suc (n+j))"
      by (rule rz_crossing_positive_moment[OF anonneg final_suc])
    show ?thesis using mpos by simp
  qed
qed

lemma rz_tail_negative_persists:
  assumes tail: "\<And>i. i < j \<Longrightarrow> \<not> b (k+i)"
    and negative: "A b k < 0" and moment_nonnegative: "0 \<le> Ma b k"
  shows "A b (k+j) < 0 \<and> 0 \<le> Ma b (k+j)"
  using tail
proof (induction j)
  case 0
  show ?case using negative moment_nonnegative by simp
next
  case (Suc j)
  have tail_prefix: "\<And>i. i < j \<Longrightarrow> \<not> b (k+i)" using Suc.prems by simp
  have tail_last: "\<not> b (k+j)" using Suc.prems by simp
  have ih: "A b (k+j) < 0 \<and> 0 \<le> Ma b (k+j)"
    by (rule Suc.IH[OF tail_prefix])
  have step: "A b (Suc (k+j)) < 0 \<and> 0 < Ma b (Suc (k+j))"
    by (rule rz_tail_negative_step[where b=b and k="k+j", OF tail_last])
      (use ih in auto)
  show ?case using step by simp
qed

lemma rz_tail_all_nonnegative:
  assumes tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and start_nonnegative: "0 \<le> A b n"
    and final_nonnegative: "0 \<le> A b (n+m)"
    and jm: "j \<le> m"
  shows "0 \<le> A b (n+j)"
proof (rule ccontr)
  assume not_nonnegative: "\<not> 0 \<le> A b (n+j)"
  have negative: "A b (n+j) < 0" using not_nonnegative by simp
  have jpos: "0 < j"
  proof (rule ccontr)
    assume "\<not> 0 < j"
    then have "j = 0" by simp
    then show False using start_nonnegative negative by simp
  qed
  have tail_prefix: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)" using tail jm by simp
  have moment_positive: "0 < Ma b (n+j)"
    by (rule rz_tail_negative_has_positive_moment[OF tail_prefix start_nonnegative negative])
  have tail_shift: "\<And>i. i < m-j \<Longrightarrow> \<not> b ((n+j)+i)"
  proof -
    fix i
    assume imj: "i < m-j"
    have jim: "j+i < m" using jm imj by arith
    have shifted: "\<not> b (n+(j+i))" by (rule tail[OF jim])
    show "\<not> b ((n+j)+i)" using shifted by (simp add: add.assoc)
  qed
  have persists: "A b ((n+j)+(m-j)) < 0 \<and> 0 \<le> Ma b ((n+j)+(m-j))"
    by (rule rz_tail_negative_persists[OF tail_shift negative])
      (use moment_positive in auto)
  have restore: "(n+j)+(m-j) = n+m" using jm by arith
  show False using persists final_nonnegative restore by simp
qed

lemma rz_ma_lower_one: "-1 \<le> Ma b k"
proof -
  have abs_bound: "abs (Ma b k) \<le> 1-beta1^k" by (rule rz_ma_bound)
  have power_nonnegative: "0 \<le> beta1^k"
    by (rule zero_le_power[OF beta1_nonneg])
  show ?thesis using abs_bound power_nonnegative by (simp add: abs_le_iff)
qed

lemma rz_tail_moment_lower:
  assumes tail: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)"
    and nonnegative: "\<And>i. i < j \<Longrightarrow> 0 \<le> A b (n+i)"
    and auxiliary: "\<And>i. i < j \<Longrightarrow> Uc b (n+i) \<le> 1"
  shows "sigmoid (-1) - (1 + sigmoid (-1)) * beta1^j \<le> Ma b (n+j)"
  using tail nonnegative auxiliary
proof (induction j)
  case 0
  have identity: "sigmoid (-1) - (1 + sigmoid (-1)) * beta1^0 = -1"
    by simp
  show ?case unfolding identity by (rule rz_ma_lower_one)
next
  case (Suc j)
  have tail_prefix: "\<And>i. i < j \<Longrightarrow> \<not> b (n+i)" using Suc.prems(1) by simp
  have nonnegative_prefix: "\<And>i. i < j \<Longrightarrow> 0 \<le> A b (n+i)"
    using Suc.prems(2) by simp
  have auxiliary_prefix: "\<And>i. i < j \<Longrightarrow> Uc b (n+i) \<le> 1"
    using Suc.prems(3) by simp
  have ih: "sigmoid (-1) - (1 + sigmoid (-1)) * beta1^j \<le> Ma b (n+j)"
    by (rule Suc.IH[OF tail_prefix nonnegative_prefix auxiliary_prefix])
  have tail_last: "\<not> b (n+j)" using Suc.prems(1) by simp
  have nonnegative_last: "0 \<le> A b (n+j)" using Suc.prems(2) by simp
  have auxiliary_last: "Uc b (n+j) \<le> 1" using Suc.prems(3) by simp
  have gradient_floor: "sigmoid (-1) \<le> Ga b (n+j)"
    by (rule rz_tail_gradient_floor[OF tail_last nonnegative_last auxiliary_last])
  have first: "beta1 * (sigmoid (-1) - (1 + sigmoid (-1)) * beta1^j)
      \<le> beta1 * Ma b (n+j)"
    by (rule mult_left_mono[OF ih beta1_nonneg])
  have second: "(1-beta1) * sigmoid (-1) \<le> (1-beta1) * Ga b (n+j)"
    by (rule mult_left_mono[OF gradient_floor]) (use beta1_lt in auto)
  have identity: "beta1 * (sigmoid (-1) - (1 + sigmoid (-1)) * beta1^j) +
      (1-beta1) * sigmoid (-1) =
      sigmoid (-1) - (1 + sigmoid (-1)) * beta1^(Suc j)"
    by (simp add: algebra_simps)
  show ?case using first second identity by simp
qed

lemma rz_tail_descent:
  assumes anonneg: "0 \<le> A b k" and rho_pos: "0 < rho"
    and moment_lower: "rho \<le> Ma b (Suc k)"
  shows "A b (Suc k) \<le> A b k - eta * rho / (1+eps)"
proof -
  have bias: "0 < 1-beta1^(Suc k)" "1-beta1^(Suc k) \<le> 1"
    using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by auto
  have scaled_bias: "rho * (1-beta1^(Suc k)) \<le> rho"
  proof -
    have "rho * (1-beta1^(Suc k)) \<le> rho * 1"
      by (rule mult_left_mono[OF bias(2)]) (use rho_pos in linarith)
    then show ?thesis by simp
  qed
  have numerator: "rho * (1-beta1^(Suc k)) \<le> Ma b (Suc k)"
    using scaled_bias moment_lower by linarith
  have mh_lower: "rho \<le> MHa b (Suc k)"
    using numerator bias(1) by (simp only: le_divide_eq if_True)
  have denominator_pos: "0 < Da b (Suc k)" by (rule rz_da_positive)
  have one_eps_pos: "0 < 1+eps" using eps_pos by linarith
  have factor_nonnegative: "0 \<le> rho / Da b (Suc k)"
    using rho_pos denominator_pos by simp
  have product: "(rho / Da b (Suc k)) * Da b (Suc k) \<le>
      (rho / Da b (Suc k)) * (1+eps)"
    by (rule mult_left_mono[OF rz_da_bounds(2) factor_nonnegative])
  have cancel: "(rho / Da b (Suc k)) * Da b (Suc k) = rho"
    using denominator_pos by simp
  have target: "rho \<le> (rho / Da b (Suc k)) * (1+eps)"
    using product cancel by linarith
  have denom_lower: "rho / (1+eps) \<le> rho / Da b (Suc k)"
    using target one_eps_pos by (subst divide_le_eq) simp
  have moment_divided: "rho / Da b (Suc k) \<le> MHa b (Suc k) / Da b (Suc k)"
    by (rule divide_right_mono[OF mh_lower]) (use denominator_pos in linarith)
  have direction: "rho / (1+eps) \<le> MHa b (Suc k) / Da b (Suc k)"
    by (rule order_trans[OF denom_lower moment_divided])
  have scaled: "eta * rho / (1+eps) \<le> eta * (MHa b (Suc k) / Da b (Suc k))"
    using mult_left_mono[OF direction, of eta] eta_pos by simp
  have contraction: "(1-eta*decay) * A b k \<le> A b k"
  proof -
    have removed: "0 \<le> (eta*decay) * A b k"
      by (rule mult_nonneg_nonneg) (use eta_pos decay_nonneg anonneg in auto)
    show ?thesis using removed by (simp add: algebra_simps)
  qed
  show ?thesis using scaled contraction by simp
qed

lemma rz_prefix_weight_upper:
  "A b (n+j) \<le> A b n + real j * (2*eta/eps)"
proof -
  have step: "A b (n+Suc i) \<le> A b (n+i) + 2*eta/eps" for i
    using rz_jump_bound[where b=b and k="n+i"] by (simp add: abs_le_iff)
  show ?thesis
    using aw_affine_iteration_upper[where n=j and f="\<lambda>i. A b (n+i)"
      and d="2*eta/eps"] step by simp
qed

theorem rz_anchor_tail_inversion:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and auxiliary: "\<And>i. i < m \<Longrightarrow> Uc b (n+i) \<le> 1"
    and anchor_bound: "A b n \<le> h"
    and burn_length: "J \<le> m"
    and burn_momentum: "(1 + sigmoid (-1)) * beta1^J \<le> sigmoid (-1) / 2"
    and takeover: "h + real J * (2*eta/eps) -
      real (m-J) * (eta * (sigmoid (-1) / 2) / (1+eps)) < 0"
  shows "A b (n+m) < 0"
proof (rule ccontr)
  assume not_negative: "\<not> A b (n+m) < 0"
  have final_nonnegative: "0 \<le> A b (n+m)" using not_negative by simp
  have start_nonnegative: "0 \<le> A b n"
    using rz_anchor_prefix[where b=b and n=n] anchor by simp
  have all_nonnegative: "0 \<le> A b (n+j)" if "j \<le> m" for j
    by (rule rz_tail_all_nonnegative[OF tail start_nonnegative final_nonnegative that])
  have moment_floor: "sigmoid (-1) / 2 \<le> Ma b (n+j)"
    if Jj: "J \<le> j" and jm: "j \<le> m" for j
  proof -
    have lower: "sigmoid (-1) - (1 + sigmoid (-1)) * beta1^j \<le> Ma b (n+j)"
      by (rule rz_tail_moment_lower)
        (use tail auxiliary all_nonnegative jm in auto)
    have power: "beta1^j \<le> beta1^J"
      by (rule aw_power_antimono) (use beta1_nonneg beta1_lt Jj in auto)
    have coefficient_positive: "0 < 1 + sigmoid (-1)"
      using sigmoid_pos[of "-1"] by linarith
    have scaled: "(1 + sigmoid (-1)) * beta1^j \<le>
        (1 + sigmoid (-1)) * beta1^J"
      by (rule mult_left_mono[OF power]) (use coefficient_positive in linarith)
    show ?thesis using lower scaled burn_momentum by linarith
  qed
  let ?d = "eta * (sigmoid (-1) / 2) / (1+eps)"
  have descent: "A b (n+J+Suc i) \<le> A b (n+J+i) - ?d"
    if im: "i < m-J" for i
  proof -
    have Jim: "J+i < m" using burn_length im by arith
    have current_nonnegative: "0 \<le> A b (n+J+i)"
      using all_nonnegative[of "J+i"] Jim by (simp add: add.assoc)
    have next_le: "Suc (J+i) \<le> m" using Jim by arith
    have next_moment: "sigmoid (-1) / 2 \<le> Ma b (Suc (n+J+i))"
      using moment_floor[of "Suc (J+i)"] next_le by (simp add: add.assoc)
    have rho_positive: "0 < sigmoid (-1) / 2" using sigmoid_pos[of "-1"] by simp
    show ?thesis
      using rz_tail_descent[where b=b and k="n+J+i" and rho="sigmoid (-1)/2",
        OF current_nonnegative rho_positive next_moment] by simp
  qed
  have total: "A b (n+m) \<le> A b (n+J) - real (m-J) * ?d"
  proof -
    have raw: "A b (n+J+(m-J)) \<le> A b (n+J+0) + real (m-J) * (-?d)"
    proof (rule aw_affine_iteration_upper[where n="m-J"
        and f="\<lambda>i. A b (n+J+i)" and d="-?d"])
      fix i
      assume "i < m-J"
      then show "A b (n+J+Suc i) \<le> A b (n+J+i) + -?d"
        using descent[of i] by linarith
    qed
    show ?thesis using raw burn_length by (simp add: algebra_simps)
  qed
  have burn: "A b (n+J) \<le> h + real J * (2*eta/eps)"
    using rz_prefix_weight_upper[where b=b and n=n and j=J] anchor_bound by linarith
  show False using total burn takeover final_nonnegative by linarith
qed

lemma rz_tail_terminal_margin:
  assumes tail: "\<not> b k" and negative: "A b k < 0"
    and moment_positive: "0 < Ma b k" and auxiliary: "Uc b k \<le> 1"
    and decay_half: "eta * decay \<le> 1/2"
    and rate_small: "eta * ((1-beta1) * sigmoid (-2) / (1+eps)) \<le> 1/2"
  shows "A b (Suc k) \<le> - eta * ((1-beta1) * sigmoid (-2) / (1+eps))"
proof -
  let ?rho = "(1-beta1) * sigmoid (-2)"
  let ?c = "?rho / (1+eps)"
  have rho_positive: "0 < ?rho"
    by (rule mult_pos_pos) (use beta1_lt sigmoid_pos[of "-2"] in auto)
  have gradient_positive: "0 < Ga b k"
    by (rule rz_tail_gradient_positive[where b=b and k=k, OF tail])
  have old_nonnegative: "0 \<le> beta1 * Ma b k"
    by (rule mult_nonneg_nonneg) (use beta1_nonneg moment_positive in auto)
  have new_positive: "0 < (1-beta1) * Ga b k"
    by (rule mult_pos_pos) (use beta1_lt gradient_positive in auto)
  have next_moment_positive: "0 < Ma b (Suc k)"
    using old_nonnegative new_positive by simp
  have next_mh_positive: "0 < MHa b (Suc k)"
    by (rule divide_pos_pos[OF next_moment_positive aw_bias_positive])
  have update_positive: "0 < eta * MHa b (Suc k) / Da b (Suc k)"
  proof -
    have numerator_positive: "0 < eta * MHa b (Suc k)"
      by (rule mult_pos_pos[OF eta_pos next_mh_positive])
    show ?thesis by (rule divide_pos_pos[OF numerator_positive rz_da_positive])
  qed
  show ?thesis
  proof (cases "A b k \<le> -1")
    case True
    have factor_nonnegative: "0 \<le> 1-eta*decay" using decay_step by simp
    have factor_half: "1/2 \<le> 1-eta*decay" using decay_half by linarith
    have scaled: "(1-eta*decay) * A b k \<le> (1-eta*decay) * (-1)"
      by (rule mult_left_mono[OF True factor_nonnegative])
    have neg_factor_raw: "-(1-eta*decay) \<le> -(1/2)"
      using factor_half by argo
    have neg_factor: "(1-eta*decay) * (-1) \<le> -1/2"
      using neg_factor_raw by simp
    have contracted: "(1-eta*decay) * A b k \<le> -1/2"
      by (rule order_trans[OF scaled neg_factor])
    have final_half: "A b (Suc k) < -1/2"
      using contracted update_positive by simp
    show ?thesis using final_half rate_small by linarith
  next
    case False
    have above_minus_one: "-1 < A b k" using False by simp
    have input: "-2 \<le> A b k - Uc b k" using above_minus_one auxiliary by linarith
    have mono: "0 \<le> sigmoid (A b k - Uc b k) - sigmoid (-2)"
      by (rule sigmoid_difference_bounds(1)[OF input])
    have gradient_shape: "Ga b k = sigmoid (A b k - Uc b k)"
      using tail by (simp add: signed_bool_def)
    have gradient_floor: "sigmoid (-2) \<le> Ga b k"
      using mono gradient_shape by linarith
    have new_lower: "?rho \<le> (1-beta1) * Ga b k"
      by (rule mult_left_mono[OF gradient_floor]) (use beta1_lt in auto)
    have moment_lower: "?rho \<le> Ma b (Suc k)"
      using old_nonnegative new_lower by simp
    have bias: "0 < 1-beta1^(Suc k)" "1-beta1^(Suc k) \<le> 1"
      using aw_bias_bounds[OF beta1_nonneg beta1_lt, of k] by auto
    have scaled_bias: "?rho * (1-beta1^(Suc k)) \<le> ?rho"
    proof -
      have "?rho * (1-beta1^(Suc k)) \<le> ?rho * 1"
        by (rule mult_left_mono[OF bias(2)]) (use rho_positive in linarith)
      then show ?thesis by simp
    qed
    have numerator: "?rho * (1-beta1^(Suc k)) \<le> Ma b (Suc k)"
      using scaled_bias moment_lower by linarith
    have mh_lower: "?rho \<le> MHa b (Suc k)"
      using numerator bias(1) by (simp only: le_divide_eq if_True)
    have denominator_positive: "0 < Da b (Suc k)" by (rule rz_da_positive)
    have one_eps_positive: "0 < 1+eps" using eps_pos by linarith
    have factor_nonnegative: "0 \<le> ?rho / Da b (Suc k)"
      using rho_positive denominator_positive by simp
    have product: "(?rho / Da b (Suc k)) * Da b (Suc k) \<le>
        (?rho / Da b (Suc k)) * (1+eps)"
      by (rule mult_left_mono[OF rz_da_bounds(2) factor_nonnegative])
    have cancel: "(?rho / Da b (Suc k)) * Da b (Suc k) = ?rho"
      using denominator_positive by simp
    have target: "?rho \<le> (?rho / Da b (Suc k)) * (1+eps)"
      using product cancel by linarith
    have denom_lower: "?c \<le> ?rho / Da b (Suc k)"
      using target one_eps_positive by (subst divide_le_eq) simp
    have moment_divided: "?rho / Da b (Suc k) \<le> MHa b (Suc k) / Da b (Suc k)"
      by (rule divide_right_mono[OF mh_lower]) (use denominator_positive in linarith)
    have direction: "?c \<le> MHa b (Suc k) / Da b (Suc k)"
      by (rule order_trans[OF denom_lower moment_divided])
    have scaled_direction: "eta * ?c \<le> eta * (MHa b (Suc k) / Da b (Suc k))"
      by (rule mult_left_mono[OF direction]) (use eta_pos in linarith)
    have contracted_nonpositive: "(1-eta*decay) * A b k \<le> 0"
      by (rule mult_nonneg_nonpos) (use decay_step negative in auto)
    show ?thesis using scaled_direction contracted_nonpositive by simp
  qed
qed

theorem rz_anchor_tail_strict_dominance:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>i. i < m \<Longrightarrow> \<not> b (n+i)"
    and total_count: "n+m \<le> N" and tail_positive: "0 < m"
    and anchor_bound: "A b n \<le> h"
    and burn_length: "J \<le> m-1"
    and burn_momentum: "(1 + sigmoid (-1)) * beta1^J \<le> sigmoid (-1) / 2"
    and takeover: "h + real J * (2*eta/eps) -
      real ((m-1)-J) * (eta * (sigmoid (-1) / 2) / (1+eps)) < 0"
    and auxiliary_small: "UB N \<le> 1"
    and decay_half: "eta * decay \<le> 1/2"
    and rate_small: "eta * ((1-beta1) * sigmoid (-2) / (1+eps)) \<le> 1/2"
    and auxiliary_dominated:
      "UB N < eta * ((1-beta1) * sigmoid (-2) / (1+eps))"
  shows "A b (n+m) < - Uc b (n+m)"
proof -
  let ?c = "(1-beta1) * sigmoid (-2) / (1+eps)"
  have coefficient_nonnegative: "0 \<le> eta * kappa^2 / eps"
    using eta_pos kappa_pos eps_pos by simp
  have auxiliary_bound: "Uc b (n+j) \<le> UB N" if jm: "j \<le> m" for j
  proof -
    have trajectory: "Uc b (n+j) \<le> real (n+j) * (eta * kappa^2 / eps)"
      by (rule rz_u_bounds(2))
    have index_le: "n+j \<le> N" using jm total_count by arith
    have scaled: "real (n+j) * (eta * kappa^2 / eps) \<le>
        real N * (eta * kappa^2 / eps)"
      by (rule mult_right_mono[OF of_nat_mono[OF index_le] coefficient_nonnegative])
    show ?thesis using trajectory scaled by simp
  qed
  have tail_prefix: "\<And>i. i < m-1 \<Longrightarrow> \<not> b (n+i)" using tail by auto
  have auxiliary_prefix: "\<And>i. i < m-1 \<Longrightarrow> Uc b (n+i) \<le> 1"
  proof -
    fix i
    assume "i < m-1"
    then have im: "i \<le> m" by arith
    have ub: "Uc b (n+i) \<le> UB N" by (rule auxiliary_bound[OF im])
    show "Uc b (n+i) \<le> 1" using ub auxiliary_small by linarith
  qed
  have penultimate_negative: "A b (n+(m-1)) < 0"
    by (rule rz_anchor_tail_inversion[where b=b and n=n and m="m-1" and J=J
          and h=h, OF anchor tail_prefix auxiliary_prefix anchor_bound burn_length
          burn_momentum takeover])
  have start_nonnegative: "0 \<le> A b n"
    using rz_anchor_prefix[where b=b and n=n] anchor by simp
  have penultimate_moment: "0 < Ma b (n+(m-1))"
    by (rule rz_tail_negative_has_positive_moment[OF tail_prefix start_nonnegative
          penultimate_negative])
  have last_index: "m-1 < m" using tail_positive by arith
  have last_tail: "\<not> b (n+(m-1))" by (rule tail[OF last_index])
  have penultimate_auxiliary: "Uc b (n+(m-1)) \<le> 1"
    using auxiliary_bound[of "m-1"] auxiliary_small by linarith
  have terminal: "A b (Suc (n+(m-1))) \<le> - eta * ?c"
    by (rule rz_tail_terminal_margin[OF last_tail penultimate_negative
          penultimate_moment penultimate_auxiliary decay_half rate_small])
  have restore: "Suc (n+(m-1)) = n+m" using tail_positive by arith
  have final_weight: "A b (n+m) \<le> - eta * ?c" using terminal restore by simp
  have final_auxiliary: "Uc b (n+m) < eta * ?c"
    using auxiliary_bound[of m] auxiliary_dominated by linarith
  show ?thesis using final_weight final_auxiliary by linarith
qed

section \<open>Strict dominance over the second coordinate and realizable metrics\<close>

abbreviation Abenign where
  "Abenign delta p N \<equiv> eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
    eta * Slack N / eps - eta * (1-p) / eps"
abbreviation Ebenign where
  "Ebenign Dsc \<equiv> (eta/eps) * (2*Dsc + beta1/(1-beta1))"
abbreviation Aattack where
  "Aattack delta N \<equiv> eta * sigmoid (-delta) / (1+eps) - eta * decay * delta -
    eta * Slack N / eps"
abbreviation Eattack where
  "Eattack \<equiv> (eta/eps) * (beta1 / ((1-beta1) * (1-beta1)))"

lemma rz_u_positive_gt:
  assumes Npos: "0 < N"
  shows "0 < Uc b N"
proof -
  obtain m where "N = Suc m" using Npos by (cases N) auto
  then show ?thesis using rz_u_positive by simp
qed

theorem rz_random_dominance:
  assumes Npos: "0 < N"
    and disc: "\<And>k. k \<le> N \<Longrightarrow>
      abs ((\<Sum>i<k. bool_value (b i)) - p * real k) \<le> Dsc"
    and drift_nonneg: "0 \<le> Abenign delta p N"
    and landing: "Uc b N < delta - 2*eta/eps - Ebenign Dsc"
    and total: "Uc b N < Abenign delta p N * real N - Ebenign Dsc"
  shows "Uc b N < A b N"
proof -
  have disc_zero: "abs ((\<Sum>i<0. bool_value (b i)) - p * real 0) \<le> Dsc"
    by (rule disc) simp
  have Dsc_nonneg: "0 \<le> Dsc" using disc_zero by simp
  have slack_nonneg: "0 \<le> Ebenign Dsc"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> eta/eps" using eta_pos eps_pos by simp
    show "0 \<le> 2*Dsc + beta1/(1-beta1)"
      using Dsc_nonneg beta1_nonneg beta1_lt by simp
  qed
  have barrier: "min (delta - 2*eta/eps - Ebenign Dsc)
      (Abenign delta p N * real N - Ebenign Dsc) \<le> A b N"
  proof (rule aw_interval_barrier[where w = "A b" and N = N
      and A = "Abenign delta p N" and B = "Ebenign Dsc"
      and S = "2*eta/eps" and r = delta])
    show "0 < N" by (rule Npos)
    show "A b 0 = 0" by simp
    show "0 \<le> Abenign delta p N" by (rule drift_nonneg)
    show "0 \<le> Ebenign Dsc" by (rule slack_nonneg)
    show "abs (A b (Suc i) - A b i) \<le> 2*eta/eps" if "i < N" for i
      by (rule rz_jump_bound)
    show "Abenign delta p N * real (v-u) - Ebenign Dsc \<le> A b v - A b u"
      if uv: "u < v" and vN: "v \<le> N"
        and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> A b i \<le> delta" for u v
    proof -
      have drift: "real (v-u) * Abenign delta p N - Ebenign Dsc \<le> A b v - A b u"
        by (rule rz_interval_drift_lower[where u=u and v=v and N=N and b=b
              and delta=delta and p=p and Dsc=Dsc])
          (use uv vN pre disc in auto)
      show ?thesis using drift by (simp add: mult.commute)
    qed
  qed
  show ?thesis using barrier landing total by linarith
qed

theorem rz_attack_dominance:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>j. n \<le> j \<Longrightarrow> j < N \<Longrightarrow> \<not> b j"
    and nN: "n < N"
    and anchor_bound: "A b n \<le> h"
    and drift_nonneg: "0 \<le> Aattack delta N"
    and landing: "h + Uc b N < delta - 2*eta/eps - Eattack"
    and total: "h + Uc b N < Aattack delta N * real (N-n) - Eattack"
  shows "A b N < - Uc b N"
proof -
  have anchor_nonneg: "0 \<le> A b n"
    using rz_anchor_prefix[where b=b and n=n] anchor by simp
  have slack_nonneg: "0 \<le> Eattack"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> eta/eps" using eta_pos eps_pos by simp
    show "0 \<le> beta1 / ((1-beta1) * (1-beta1))"
      using beta1_nonneg beta1_lt by simp
  qed
  have barrier: "min (delta - 2*eta/eps - Eattack)
      (Aattack delta N * real (N-n) - Eattack) \<le> A b n - A b (n + (N-n))"
  proof (rule aw_interval_barrier[where w = "\<lambda>j. A b n - A b (n+j)"
      and N = "N-n" and A = "Aattack delta N" and B = Eattack
      and S = "2*eta/eps" and r = delta])
    show "0 < N-n" using nN by simp
    show "A b n - A b (n+0) = 0" by simp
    show "0 \<le> Aattack delta N" by (rule drift_nonneg)
    show "0 \<le> Eattack" by (rule slack_nonneg)
    show "abs ((A b n - A b (n+Suc i)) - (A b n - A b (n+i))) \<le> 2*eta/eps"
      if "i < N-n" for i
    proof -
      have shape: "(A b n - A b (n+Suc i)) - (A b n - A b (n+i)) =
          - (A b (Suc (n+i)) - A b (n+i))"
        by simp
      have jump: "abs (A b (Suc (n+i)) - A b (n+i)) \<le> 2*eta/eps"
        by (rule rz_jump_bound)
      show ?thesis using shape jump by simp
    qed
    show "Aattack delta N * real (v-u) - Eattack \<le>
        (A b n - A b (n+v)) - (A b n - A b (n+u))"
      if uv: "u < v" and vN: "v \<le> N-n"
        and pre: "\<And>i. u \<le> i \<Longrightarrow> i < v \<Longrightarrow> A b n - A b (n+i) \<le> delta" for u v
    proof -
      have shifted: "n+u \<le> n+v" using uv by simp
      have bound: "n+v \<le> N" using vN nN by simp
      have tail_shift: "\<not> b j" if "n+u \<le> j" and "j < n+v" for j
        using tail that bound by simp
      have pre_shift: "- delta \<le> A b i" if "n+u \<le> i" and "i < n+v" for i
      proof -
        have index: "u \<le> i-n" "i-n < v" using that by auto
        have step: "A b n - A b (n+(i-n)) \<le> delta"
          by (rule pre) (use index in auto)
        have restore: "n+(i-n) = i" using that by simp
        show ?thesis using step restore anchor_nonneg by simp
      qed
      have drift: "A b (n+v) - A b (n+u) \<le>
          real ((n+v)-(n+u)) * (eta * decay * delta -
            eta * sigmoid (-delta) / (1+eps) + eta * Slack N / eps) + Eattack"
        by (rule rz_interval_drift_upper[where u="n+u" and v="n+v" and N=N
              and b=b and delta=delta])
          (use shifted bound tail_shift pre_shift in auto)
      have drift2: "A b (n+v) - A b (n+u) \<le>
          real (v-u) * (eta * decay * delta -
            eta * sigmoid (-delta) / (1+eps) + eta * Slack N / eps) + Eattack"
        using drift by simp
      have flip: "real (v-u) * (eta * decay * delta -
            eta * sigmoid (-delta) / (1+eps) + eta * Slack N / eps) =
          - (Aattack delta N * real (v-u))"
        by (simp add: algebra_simps)
      show ?thesis using drift2 flip by argo
    qed
  qed
  have restore: "n + (N-n) = N" using nN by simp
  show ?thesis using barrier restore anchor_bound landing total by simp
qed

corollary rz_attack_metrics:
  assumes anchor: "\<And>i. i < n \<Longrightarrow> b i"
    and tail: "\<And>j. n \<le> j \<Longrightarrow> j < N \<Longrightarrow> \<not> b j"
    and nN: "n < N"
    and anchor_bound: "A b n \<le> h"
    and drift_nonneg: "0 \<le> Aattack delta N"
    and landing: "h + Uc b N < delta - 2*eta/eps - Eattack"
    and total: "h + Uc b N < Aattack delta N * real (N-n) - Eattack"
  shows "realizable_test_risk epsilon (A b N) (Uc b N) = 1 - epsilon"
    and "realizable_test_auc epsilon (A b N) (Uc b N) = 2*epsilon - epsilon^2"
proof -
  have upos: "0 < Uc b N" using nN by (simp add: rz_u_positive_gt)
  have dominance: "A b N < - Uc b N"
    by (rule rz_attack_dominance[OF anchor tail nN anchor_bound drift_nonneg
          landing total])
  show "realizable_test_risk epsilon (A b N) (Uc b N) = 1 - epsilon"
    by (rule realizable_test_risk_negative[OF upos dominance])
  show "realizable_test_auc epsilon (A b N) (Uc b N) = 2*epsilon - epsilon^2"
    by (rule realizable_test_auc_attack[OF upos dominance])
qed

corollary rz_random_metrics:
  assumes Npos: "0 < N"
    and disc: "\<And>k. k \<le> N \<Longrightarrow>
      abs ((\<Sum>i<k. bool_value (b i)) - p * real k) \<le> Dsc"
    and drift_nonneg: "0 \<le> Abenign delta p N"
    and landing: "Uc b N < delta - 2*eta/eps - Ebenign Dsc"
    and total: "Uc b N < Abenign delta p N * real N - Ebenign Dsc"
  shows "realizable_test_risk epsilon (A b N) (Uc b N) = epsilon"
    and "realizable_test_auc epsilon (A b N) (Uc b N) = 1 - epsilon^2"
proof -
  have upos: "0 < Uc b N" using Npos by (rule rz_u_positive_gt)
  have dominance: "Uc b N < A b N"
    by (rule rz_random_dominance[OF Npos disc drift_nonneg landing total])
  show "realizable_test_risk epsilon (A b N) (Uc b N) = epsilon"
    by (rule realizable_test_risk_positive[OF upos dominance])
  show "realizable_test_auc epsilon (A b N) (Uc b N) = 1 - epsilon^2"
    by (rule realizable_test_auc_random[OF upos dominance])
qed

section \<open>Random presentation order in the realizable model\<close>

text \<open>
  The hypotheses are stated with the uniform auxiliary bound UB N, which
  dominates the actual auxiliary margin of every presentation order, so the
  same numeric conditions cover the whole probability space.
\<close>

theorem rz_random_order_benign_probability:
  fixes conf delta epsilon :: real
  assumes Npos: "0 < N" and sample_size: "n \<le> N"
    and conf_positive: "0 < conf" and conf_at_most_one: "conf \<le> 1"
    and drift_nonneg: "0 \<le> Abenign delta (real n / real N) N"
    and landing: "UB N < delta - 2*eta/eps -
      Ebenign (sqrt (real N / 2 * ln (2 * real N / conf)))"
    and total: "UB N < Abenign delta (real n / real N) N * real N -
      Ebenign (sqrt (real N / 2 * ln (2 * real N / conf)))"
  shows "1 - conf \<le> uniform_probability (binary_orders n N)
    {xs. realizable_test_risk epsilon (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) =
           epsilon \<and>
         realizable_test_auc epsilon (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) =
           1 - epsilon^2}"
proof -
  let ?Omega = "binary_orders n N"
  let ?u = "sqrt (real N / 2 * ln (2 * real N / conf))"
  let ?bad = "{xs. ?u \<le> binary_max_centered_prefix n N xs}"
  let ?good = "{xs. realizable_test_risk epsilon
      (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) = epsilon \<and>
    realizable_test_auc epsilon
      (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) = 1 - epsilon^2}"
  have bad_bound: "uniform_probability ?Omega ?bad \<le> conf"
    by (rule uniform_binary_order_max_prefix_confidence[OF Npos
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
        by (rule binary_innovation_prefix_le_max[OF Npos sample_size
              xs_order kN])
      show ?thesis using prefix_eq le_max prefix_good by simp
    qed
    have auxiliary: "Uc (\<lambda>i. xs ! i) N \<le> UB N"
      by (rule rz_u_bounds(2))
    have landing_xs: "Uc (\<lambda>i. xs ! i) N < delta - 2*eta/eps - Ebenign ?u"
      using auxiliary landing by linarith
    have total_xs: "Uc (\<lambda>i. xs ! i) N <
        Abenign delta (real n / real N) N * real N - Ebenign ?u"
      using auxiliary total by linarith
    have risk: "realizable_test_risk epsilon
        (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) = epsilon"
      by (rule rz_random_metrics(1)[where b = "\<lambda>i. xs ! i" and N = N
            and p = "real n / real N" and Dsc = ?u and delta = delta])
        (use Npos disc drift_nonneg landing_xs total_xs in auto)
    have auc: "realizable_test_auc epsilon
        (A (\<lambda>i. xs ! i) N) (Uc (\<lambda>i. xs ! i) N) = 1 - epsilon^2"
      by (rule rz_random_metrics(2)[where b = "\<lambda>i. xs ! i" and N = N
            and p = "real n / real N" and Dsc = ?u and delta = delta])
        (use Npos disc drift_nonneg landing_xs total_xs in auto)
    show "xs \<in> ?good" using risk auc by simp
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
