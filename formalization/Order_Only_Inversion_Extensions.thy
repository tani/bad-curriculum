theory Order_Only_Inversion_Extensions
  imports Finite_Population_Hoeffding
begin
text \<open>linear_score: 線形モデルの重みと信号からスコアを定める。\<close>
definition linear_score :: "real \<Rightarrow> real \<Rightarrow> real" where
  "linear_score w s = w * s"

text \<open>clean_signed_margin: 更新後の分類マージンを評価する。\<close>
lemma clean_signed_margin:
  assumes signal_sign: "s = 1 \<or> s = -1"
  shows "clean_label s t * linear_score w s = w * t"
  using signal_sign unfolding clean_label_def linear_score_def
  by auto

text \<open>zero_one_margin_loss: 符号付きマージンに対する零一損失を定める。\<close>
definition zero_one_margin_loss :: "real \<Rightarrow> real" where
  "zero_one_margin_loss z = (if 0 < z then 0 else 1)"

text \<open>probability_parameter: 確率パラメータが単位区間に入る条件を定める。\<close>
definition probability_parameter :: "real \<Rightarrow> bool" where
  "probability_parameter epsilon \<longleftrightarrow> 0 \<le> epsilon \<and> epsilon \<le> 1"

text \<open>probability_parameter_bounds: 誤差または状態の明示的な上界を与える。\<close>
lemma probability_parameter_bounds:
  assumes "probability_parameter epsilon"
  shows "0 \<le> epsilon" and "epsilon \<le> 1"
  using assms unfolding probability_parameter_def by auto

text \<open>clean_test_risk: 正常データと反転データを混ぜたテストリスクを定める。\<close>
definition clean_test_risk :: "real \<Rightarrow> real \<Rightarrow> real" where
  "clean_test_risk epsilon w =
    (1 - epsilon) * zero_one_margin_loss w +
      epsilon * zero_one_margin_loss (-w)"

text \<open>clean_test_risk_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma clean_test_risk_positive:
  assumes w_positive: "0 < w"
  shows "clean_test_risk epsilon w = epsilon"
  using w_positive unfolding clean_test_risk_def zero_one_margin_loss_def
  by simp

text \<open>clean_test_risk_negative: 対象量が負であること、または負側の評価を示す。\<close>
lemma clean_test_risk_negative:
  assumes w_negative: "w < 0"
  shows "clean_test_risk epsilon w = 1 - epsilon"
  using w_negative unfolding clean_test_risk_def zero_one_margin_loss_def
  by simp

text \<open>clean_test_risk_reversal: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma clean_test_risk_reversal:
  assumes epsilon_nonnegative: "0 \<le> epsilon"
    and epsilon_below_half: "epsilon < 1 / 2"
    and attack_negative: "w_attack < 0"
    and random_positive: "0 < w_random"
  shows "clean_test_risk epsilon w_attack = 1 - epsilon"
    and "clean_test_risk epsilon w_random = epsilon"
    and "clean_test_risk epsilon w_random < clean_test_risk epsilon w_attack"
proof -
  have attack_risk: "clean_test_risk epsilon w_attack = 1 - epsilon"
    by (rule clean_test_risk_negative[OF attack_negative])
  have random_risk: "clean_test_risk epsilon w_random = epsilon"
    by (rule clean_test_risk_positive[OF random_positive])
  show "clean_test_risk epsilon w_attack = 1 - epsilon"
    by (rule attack_risk)
  show "clean_test_risk epsilon w_random = epsilon"
    by (rule random_risk)
  show "clean_test_risk epsilon w_random < clean_test_risk epsilon w_attack"
    using attack_risk random_risk epsilon_below_half by linarith
qed

text \<open>auc_pair_credit: 正例スコアと負例スコアの一対比較に与える AUC 信用を定める。\<close>
definition auc_pair_credit :: "real \<Rightarrow> real \<Rightarrow> real" where
  "auc_pair_credit positive_score negative_score =
    (if negative_score < positive_score then 1
     else if negative_score = positive_score then 1 / 2 else 0)"

text \<open>clean_test_auc: 正常分布と反転分布のスコア比較から AUC を定める。\<close>
definition clean_test_auc :: "real \<Rightarrow> real \<Rightarrow> real" where
  "clean_test_auc epsilon w =
    (1 - epsilon)^2 * auc_pair_credit w (-w) +
    (1 - epsilon) * epsilon * auc_pair_credit w w +
    epsilon * (1 - epsilon) * auc_pair_credit (-w) (-w) +
    epsilon^2 * auc_pair_credit (-w) w"

text \<open>clean_test_auc_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma clean_test_auc_positive:
  assumes w_positive: "0 < w"
  shows "clean_test_auc epsilon w = 1 - epsilon"
  unfolding clean_test_auc_def auc_pair_credit_def
  using w_positive by (simp add: power2_eq_square algebra_simps)

text \<open>clean_test_auc_negative: 対象量が負であること、または負側の評価を示す。\<close>
lemma clean_test_auc_negative:
  assumes w_negative: "w < 0"
  shows "clean_test_auc epsilon w = epsilon"
  unfolding clean_test_auc_def auc_pair_credit_def
  using w_negative by (simp add: power2_eq_square algebra_simps)

text \<open>clean_test_auc_reversal: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma clean_test_auc_reversal:
  assumes attack_negative: "w_attack < 0"
    and random_positive: "0 < w_random"
  shows "clean_test_auc epsilon w_attack = epsilon"
    and "clean_test_auc epsilon w_random = 1 - epsilon"
  by (rule clean_test_auc_negative[OF attack_negative],
      rule clean_test_auc_positive[OF random_positive])

text \<open>selector_signed_margin: セレクタの信号に対する符号付きマージンを定める。\<close>
definition selector_signed_margin ::
    "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "selector_signed_margin a s t = clean_label s t * linear_score a s"

text \<open>selector_signed_margin_eq: 更新後の分類マージンを評価する。\<close>
lemma selector_signed_margin_eq:
  assumes signal_sign: "s = 1 \<or> s = -1"
  shows "selector_signed_margin a s t = a * t"
  unfolding selector_signed_margin_def
  by (rule clean_signed_margin[OF signal_sign])

text \<open>selector_misclassifies_iff_tail: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma selector_misclassifies_iff_tail:
  assumes selector_positive: "0 < a"
    and signal_sign: "s = 1 \<or> s = -1"
    and subgroup_sign: "t = 1 \<or> t = -1"
  shows "selector_signed_margin a s t < 0 \<longleftrightarrow> t = -1"
  unfolding selector_signed_margin_eq[OF signal_sign]
  using selector_positive subgroup_sign by auto

text \<open>structured_example: 信号、サブグループ、識別子からなる構造化データ型を表す。\<close>
type_synonym structured_example = "real \<times> real \<times> (bool \<times> nat)"

text \<open>example_label: 構造化例のクリーンラベルを取り出す。\<close>
definition example_label :: "structured_example \<Rightarrow> real" where
  "example_label x = (case x of (s, t, r) \<Rightarrow> s * t)"

text \<open>example_identity: 構造化例の識別子を取り出す。\<close>
definition example_identity :: "structured_example \<Rightarrow> bool \<times> nat" where
  "example_identity x = (case x of (s, t, r) \<Rightarrow> r)"

text \<open>example_signal: 構造化例の信号座標を取り出す。\<close>
definition example_signal :: "structured_example \<Rightarrow> real" where
  "example_signal x = (case x of (s, t, r) \<Rightarrow> s)"

text \<open>example_score: 重み付き構造化例スコアを定める。\<close>
definition example_score :: "real \<Rightarrow> structured_example \<Rightarrow> real" where
  "example_score w x = w * example_signal x"

text \<open>example_margin_loss: 構造化例の分類マージン損失を定める。\<close>
definition example_margin_loss :: "real \<Rightarrow> structured_example \<Rightarrow> real" where
  "example_margin_loss w x =
    zero_one_margin_loss (example_label x * example_score w x)"

text \<open>empirical_risk: 有限リスト上の経験リスクを定める。\<close>
definition empirical_risk :: "structured_example list \<Rightarrow> real \<Rightarrow> real" where
  "empirical_risk xs w =
    (if xs = [] then 0
     else sum_list (map (example_margin_loss w) xs) / real (length xs))"

text \<open>positive_scores: ラベルが正の例のスコア列を抽出する。\<close>
definition positive_scores ::
    "structured_example list \<Rightarrow> real \<Rightarrow> real list" where
  "positive_scores xs w =
    map (example_score w) (filter (\<lambda>x. example_label x = 1) xs)"

text \<open>negative_scores: ラベルが負の例のスコア列を抽出する。\<close>
definition negative_scores ::
    "structured_example list \<Rightarrow> real \<Rightarrow> real list" where
  "negative_scores xs w =
    map (example_score w) (filter (\<lambda>x. example_label x = -1) xs)"

text \<open>empirical_auc: 有限リストから経験 AUC を定める。\<close>
definition empirical_auc :: "structured_example list \<Rightarrow> real \<Rightarrow> real" where
  "empirical_auc xs w =
    (let ps = positive_scores xs w; ns = negative_scores xs w in
      if ps = [] \<or> ns = [] then 0
      else sum_list (map (\<lambda>p. sum_list (map (auc_pair_credit p) ns)) ps) /
        (real (length ps) * real (length ns)))"

text \<open>balanced_block: 一つのサブグループについて符号を均衡させたブロックを構成する。\<close>
definition balanced_block :: "real \<Rightarrow> nat \<Rightarrow> structured_example list" where
  "balanced_block t k =
    map (\<lambda>i. (1, t, (True, i))) [0..<k] @
    map (\<lambda>i. (-1, t, (False, i))) [0..<k]"

text \<open>balanced_block_length: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma balanced_block_length:
  "length (balanced_block t k) = 2 * k"
  unfolding balanced_block_def by simp

text \<open>map_constant_upt: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma map_constant_upt:
  "map (\<lambda>i. c) [0..<k] = replicate k c"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. c) [0..<k]) = length (replicate k c)"
    by simp
  fix i
  assume "i < length (map (\<lambda>i. c) [0..<k])"
  then show "map (\<lambda>i. c) [0..<k] ! i = replicate k c ! i"
    by simp
qed

text \<open>balanced_test_pool: アンカーとテールの均衡ブロックを連結したテスト母集団を定める。\<close>
definition balanced_test_pool ::
    "nat \<Rightarrow> nat \<Rightarrow> structured_example list" where
  "balanced_test_pool anchor_count tail_count =
    balanced_block 1 anchor_count @ balanced_block (-1) tail_count"

text \<open>balanced_block_margin_losses: 更新後の分類マージンを評価する。\<close>
lemma balanced_block_margin_losses:
  "map (example_margin_loss w) (balanced_block t k) =
    replicate (2 * k) (zero_one_margin_loss (w * t))"
  proof -
  have positive_function:
    "example_margin_loss w \<circ> (\<lambda>i. (1, t, (True, i))) =
      (\<lambda>i. zero_one_margin_loss (w * t))"
    by (rule ext)
      (simp add: example_margin_loss_def example_label_def example_score_def
        example_signal_def algebra_simps)
  have negative_function:
    "example_margin_loss w \<circ> (\<lambda>i. (-1, t, (False, i))) =
      (\<lambda>i. zero_one_margin_loss (w * t))"
    by (rule ext)
      (simp add: example_margin_loss_def example_label_def example_score_def
        example_signal_def algebra_simps)
  show ?thesis
    unfolding balanced_block_def map_append map_map positive_function
      negative_function map_constant_upt
    by (simp only: mult_2 replicate_add)
qed

text \<open>empirical_risk_balanced_test_pool: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma empirical_risk_balanced_test_pool:
  assumes nonempty: "0 < anchor_count + tail_count"
  shows "empirical_risk (balanced_test_pool anchor_count tail_count) w =
    clean_test_risk (real tail_count / real (anchor_count + tail_count)) w"
proof -
  have count_nonzero: "anchor_count + tail_count \<noteq> 0"
    using nonempty by auto
  have denominator_positive: "0 < real (anchor_count + tail_count)"
    using nonempty by (simp only: of_nat_0_less_iff)
  have denominator_nonzero: "real (anchor_count + tail_count) \<noteq> 0"
    using denominator_positive by linarith
  have pool_length:
    "length (balanced_test_pool anchor_count tail_count) =
      2 * (anchor_count + tail_count)"
    unfolding balanced_test_pool_def
    by (simp add: balanced_block_length distrib_left)
  have pool_nonempty: "balanced_test_pool anchor_count tail_count \<noteq> []"
    using pool_length nonempty by auto
  have expanded_pool_nonempty:
    "balanced_block 1 anchor_count @ balanced_block (-1) tail_count \<noteq> []"
    using pool_nonempty unfolding balanced_test_pool_def by assumption
  have empirical_nonempty:
    "empirical_risk (balanced_test_pool anchor_count tail_count) w =
      sum_list (map (example_margin_loss w)
        (balanced_test_pool anchor_count tail_count)) /
      real (length (balanced_test_pool anchor_count tail_count))"
    unfolding empirical_risk_def
    by (simp only: if_not_P[OF pool_nonempty])
  have expansion:
    "empirical_risk (balanced_test_pool anchor_count tail_count) w =
      (real (2 * anchor_count) * zero_one_margin_loss w +
       real (2 * tail_count) * zero_one_margin_loss (- w)) /
       real (2 * (anchor_count + tail_count))"
    using empirical_nonempty
    unfolding balanced_test_pool_def
    by (simp add: balanced_block_length balanced_block_margin_losses
        sum_list_replicate)
  have doubled_denominator:
    "2 * real anchor_count + 2 * real tail_count =
      2 * (real anchor_count + real tail_count)"
    by algebra
  have inverse_cancel:
    "(real anchor_count + real tail_count) *
      inverse (real anchor_count + real tail_count) = 1"
    using denominator_nonzero by simp
  have inverse_two: "inverse (2::real) = 0.5"
    by simp
  show ?thesis
    unfolding clean_test_risk_def
    apply (subst expansion)
    apply (simp only: of_nat_mult of_nat_add)
    apply (simp only: divide_inverse inverse_mult_distrib)
    apply simp
    apply (subst inverse_cancel[symmetric])
    apply algebra
    done
qed

text \<open>balanced_block_labels: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma balanced_block_labels:
  "map example_label (balanced_block t k) =
    replicate k t @ replicate k (-t)"
proof -
  have positive_function:
    "((\<lambda>(s, t, r). s * t) \<circ> (\<lambda>i. (1, t, (True, i)))) =
      (\<lambda>i. t)"
    by (rule ext) simp
  have negative_function:
    "((\<lambda>(s, t, r). s * t) \<circ> (\<lambda>i. (-1, t, (False, i)))) =
      (\<lambda>i. -t)"
    by (rule ext) simp
  show ?thesis
    unfolding balanced_block_def example_label_def map_append map_map
      positive_function negative_function map_constant_upt by (rule refl)

qed

text \<open>map_upt_ext_constant: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma map_upt_ext_constant:
  assumes pointwise: "\<And>i. i < k \<Longrightarrow> f i = c"
  shows "map f [0..<k] = replicate k c"
  unfolding map_constant_upt[symmetric]
  by (rule map_cong) (use pointwise in auto)

text \<open>balanced_block_positive_scores: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma balanced_block_positive_scores:
  assumes subgroup_sign: "t = 1 \<or> t = -1"
  shows "positive_scores (balanced_block t k) w =
    (if t = 1 then replicate k w else replicate k (-w))"
  proof -
  have positive_score_function:
    "((\<lambda>x. w * (case x of (s, t, r) \<Rightarrow> s)) \<circ>
      (\<lambda>i. (1, t, (True, i)))) = (\<lambda>i. w)"
    by (rule ext) simp
  have negative_score_function:
    "((\<lambda>x. w * (case x of (s, t, r) \<Rightarrow> s)) \<circ>
      (\<lambda>i. (-1, t, (False, i)))) = (\<lambda>i. -w)"
    by (rule ext) simp
  show ?thesis
    using subgroup_sign
    unfolding positive_scores_def balanced_block_def example_label_def
      example_score_def example_signal_def map_append map_map
      positive_score_function negative_score_function map_constant_upt
    apply (elim disjE)
    apply simp
    apply (rule map_upt_ext_constant)
    apply simp
    apply simp
    apply (rule map_upt_ext_constant)
    apply simp
    done
qed

text \<open>balanced_block_negative_scores: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma balanced_block_negative_scores:
  assumes subgroup_sign: "t = 1 \<or> t = -1"
  shows "negative_scores (balanced_block t k) w =
    (if t = 1 then replicate k (-w) else replicate k w)"
  using subgroup_sign
  unfolding negative_scores_def balanced_block_def example_label_def
    example_score_def example_signal_def
  apply (elim disjE)
  apply simp
  apply (rule map_upt_ext_constant)
  apply simp
  apply simp
  apply (rule map_upt_ext_constant)
  apply simp
  done

text \<open>positive_scores_append: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma positive_scores_append [simp]:
  "positive_scores (xs @ ys) w =
    positive_scores xs w @ positive_scores ys w"
  unfolding positive_scores_def by simp

text \<open>negative_scores_append: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma negative_scores_append [simp]:
  "negative_scores (xs @ ys) w =
    negative_scores xs w @ negative_scores ys w"
  unfolding negative_scores_def by simp

text \<open>balanced_test_pool_positive_scores: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma balanced_test_pool_positive_scores:
  "positive_scores (balanced_test_pool anchor_count tail_count) w =
    replicate anchor_count w @ replicate tail_count (-w)"
  unfolding balanced_test_pool_def
  by (simp add: balanced_block_positive_scores)

text \<open>balanced_test_pool_negative_scores: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma balanced_test_pool_negative_scores:
  "negative_scores (balanced_test_pool anchor_count tail_count) w =
    replicate anchor_count (-w) @ replicate tail_count w"
  unfolding balanced_test_pool_def
  by (simp add: balanced_block_negative_scores)

text \<open>empirical_auc_balanced_test_pool: スコアから導かれるリスクまたは AUC の値を計算する。\<close>
lemma empirical_auc_balanced_test_pool:
  assumes nonempty: "0 < anchor_count + tail_count"
  shows "empirical_auc (balanced_test_pool anchor_count tail_count) w =
    clean_test_auc (real tail_count / real (anchor_count + tail_count)) w"
proof -
  have scores_nonempty:
    "replicate anchor_count w @ replicate tail_count (-w) \<noteq> []"
    "replicate anchor_count (-w) @ replicate tail_count w \<noteq> []"
    using nonempty by auto
  have score_condition:
    "\<not> (replicate anchor_count w @ replicate tail_count (-w) = [] \<or>
       replicate anchor_count (-w) @ replicate tail_count w = [])"
    using scores_nonempty by blast
  have denominator_positive:
    "0 < real (anchor_count + tail_count)"
    using nonempty by (simp only: of_nat_0_less_iff)
  have denominator_nonzero:
    "real anchor_count + real tail_count \<noteq> 0"
    using denominator_positive
    unfolding of_nat_add
    by linarith
  have inverse_cancel:
    "(real anchor_count + real tail_count) *
      inverse (real anchor_count + real tail_count) = 1"
    using denominator_nonzero by simp
  show ?thesis
    unfolding empirical_auc_def clean_test_auc_def Let_def
      balanced_test_pool_positive_scores balanced_test_pool_negative_scores
    apply (simp only: if_not_P[OF score_condition])
    apply (simp add: sum_list_replicate power2_eq_square)
    apply (simp only: divide_inverse inverse_mult_distrib)
    apply (subst inverse_cancel[symmetric])
    apply (subst inverse_cancel[symmetric])
    apply (subst inverse_cancel[symmetric])
    apply (subst inverse_cancel[symmetric])
    apply algebra
    done
qed

text \<open>balanced_block_identities_distinct: 定義と後続の反転解析で用いる基本性質を示す。\<close>
lemma balanced_block_identities_distinct:

  "distinct (map example_identity (balanced_block t k))"
proof -
  have positive_function:
    "((\<lambda>(s, t, r). r) \<circ> (\<lambda>i. (1, t, (True, i)))) = Pair True"
    by (rule ext) simp
  have negative_function:
    "((\<lambda>(s, t, r). r) \<circ> (\<lambda>i. (-1, t, (False, i)))) = Pair False"
    by (rule ext) simp
  have positive_distinct: "distinct (map (Pair True) [0..<k])"
    by (simp add: distinct_map inj_on_def)

  have negative_distinct: "distinct (map (Pair False) [0..<k])"
    by (simp add: distinct_map inj_on_def)

  have disjoint:
    "set (map (Pair True) [0..<k]) \<inter>
      set (map (Pair False) [0..<k]) = {}"
    by auto
  show ?thesis
    unfolding balanced_block_def example_identity_def map_append map_map
      positive_function negative_function
    using positive_distinct negative_distinct disjoint by simp
qed
text \<open>count_list_replicate_same: カリキュラムの個数または母集団分解を整理する。\<close>

lemma count_list_replicate_same [simp]:
  "count_list (replicate k x) x = k"
  by (induction k) simp_all
text \<open>count_list_replicate_different: カリキュラムの個数または母集団分解を整理する。\<close>

lemma count_list_replicate_different [simp]:
  assumes different: "x \<noteq> y"
  shows "count_list (replicate k x) y = 0"
  using different by (induction k) simp_all
text \<open>balanced_block_label_counts: カリキュラムの個数または母集団分解を整理する。\<close>

lemma balanced_block_label_counts:
  assumes subgroup_sign: "t = 1 \<or> t = -1"
  shows "count_list (map example_label (balanced_block t k)) 1 = k"
    and "count_list (map example_label (balanced_block t k)) (-1) = k"
  using subgroup_sign unfolding balanced_block_labels
  by auto
text \<open>anchor_and_tail_blocks_balanced: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma anchor_and_tail_blocks_balanced:
  shows "count_list (map example_label (balanced_block 1 k)) 1 = k \<and>
      count_list (map example_label (balanced_block 1 k)) (-1) = k"
    and "count_list (map example_label (balanced_block (-1) k)) 1 = k \<and>
      count_list (map example_label (balanced_block (-1) k)) (-1) = k"
  using balanced_block_label_counts[of 1 k]
    balanced_block_label_counts[of "-1" k] by auto

text \<open>realizable_test_auc: 二座標の実現可能モデルにおけるテスト AUC を定める。\<close>

definition realizable_test_auc ::
    "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "realizable_test_auc epsilon a u =
    (1 - epsilon)^2 * auc_pair_credit (a + u) (-a - u) +
    (1 - epsilon) * epsilon * auc_pair_credit (a + u) (a - u) +
    epsilon * (1 - epsilon) * auc_pair_credit (-a + u) (-a - u) +
    epsilon^2 * auc_pair_credit (-a + u) (a - u)"
text \<open>realizable_test_auc_random: スコアから導かれるリスクまたは AUC の値を計算する。\<close>

lemma realizable_test_auc_random:
  assumes u_positive: "0 < u"
    and dominant_positive: "u < a"
  shows "realizable_test_auc epsilon a u = 1 - epsilon^2"
proof -
  have anchor_pair: "-a - u < a + u" using u_positive dominant_positive by linarith
  have anchor_tail_pair: "a - u < a + u" using u_positive by linarith
  have tail_anchor_pair: "-a - u < -a + u" using u_positive by linarith
  have tail_pair: "-a + u < a - u" using dominant_positive by linarith
  show ?thesis
    unfolding realizable_test_auc_def auc_pair_credit_def
    using anchor_pair anchor_tail_pair tail_anchor_pair tail_pair
    by (simp add: power2_eq_square algebra_simps)
qed
text \<open>realizable_test_auc_attack: スコアから導かれるリスクまたは AUC の値を計算する。\<close>

lemma realizable_test_auc_attack:
  assumes u_positive: "0 < u"
    and dominant_negative: "a < -u"
  shows "realizable_test_auc epsilon a u = 2 * epsilon - epsilon^2"
proof -
  have anchor_pair: "a + u < -a - u" using dominant_negative by linarith
  have anchor_tail_pair: "a - u < a + u" using u_positive by linarith
  have tail_anchor_pair: "-a - u < -a + u" using u_positive by linarith
  have tail_pair: "a - u < -a + u"
    using dominant_negative u_positive by linarith

  show ?thesis
    unfolding realizable_test_auc_def auc_pair_credit_def
    using anchor_pair anchor_tail_pair tail_anchor_pair tail_pair
    by (simp add: power2_eq_square algebra_simps)
qed
text \<open>curriculum_scale: カリキュラム段階の基本スケールを定める。\<close>

definition curriculum_scale :: "nat \<Rightarrow> nat" where
  "curriculum_scale k = 2 * (k + 2)"
text \<open>curriculum_population: 基本スケールから全母集団サイズを定める。\<close>

definition curriculum_population :: "nat \<Rightarrow> nat" where
  "curriculum_population k = curriculum_scale k ^ 6"
text \<open>curriculum_tail_count: 基本スケールからテール個数を定める。\<close>

definition curriculum_tail_count :: "nat \<Rightarrow> nat" where
  "curriculum_tail_count k = curriculum_scale k ^ 5"
text \<open>curriculum_anchor_count: 全母集団からテールを引いたアンカー個数を定める。\<close>

definition curriculum_anchor_count :: "nat \<Rightarrow> nat" where
  "curriculum_anchor_count k =
    curriculum_population k - curriculum_tail_count k"
text \<open>curriculum_learning_rate: 段階依存の学習率を定める。\<close>

definition curriculum_learning_rate :: "nat \<Rightarrow> real" where
  "curriculum_learning_rate k = 1 / real (curriculum_scale k) ^ 4"
text \<open>curriculum_confidence: ランダム順序評価に用いる信頼度誤差を定める。\<close>

definition curriculum_confidence :: "nat \<Rightarrow> real" where
  "curriculum_confidence k = 1 / real (curriculum_scale k) ^ 12"
text \<open>curriculum_realizable_scale: 実現可能モデルの二座標スケールを定める。\<close>

definition curriculum_realizable_scale :: "nat \<Rightarrow> real" where
  "curriculum_realizable_scale k = 1 / real (curriculum_scale k) ^ 3"
text \<open>curriculum_tail_ratio: テール個数の母集団比率を定める。\<close>

definition curriculum_tail_ratio :: "nat \<Rightarrow> real" where
  "curriculum_tail_ratio k =
    real (curriculum_tail_count k) / real (curriculum_population k)"
text \<open>curriculum_scale_at_least_four: 対象量の下界を示す。\<close>

lemma curriculum_scale_at_least_four:
  "4 \<le> curriculum_scale k"
  unfolding curriculum_scale_def by simp
text \<open>curriculum_counts: カリキュラムの個数または母集団分解を整理する。\<close>

lemma curriculum_counts:
  "curriculum_tail_count k + curriculum_anchor_count k =
    curriculum_population k"
proof -
  have scale_at_least_one: "1 \<le> curriculum_scale k"
    using curriculum_scale_at_least_four[of k] by simp
  have tail_le_population:
    "curriculum_tail_count k \<le> curriculum_population k"
  proof -
    have "curriculum_scale k ^ 5 \<le>
        curriculum_scale k ^ 5 * curriculum_scale k"
      using scale_at_least_one by simp
    also have "... = curriculum_scale k ^ 6" by algebra
    finally show ?thesis
      unfolding curriculum_tail_count_def curriculum_population_def .
  qed
  show ?thesis
    unfolding curriculum_anchor_count_def using tail_le_population by simp
qed
text \<open>curriculum_tail_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma curriculum_tail_positive:
  "0 < curriculum_tail_count k"
  unfolding curriculum_tail_count_def curriculum_scale_def by simp
text \<open>curriculum_tail_smaller: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma curriculum_tail_smaller:
  "curriculum_tail_count k < curriculum_anchor_count k"
proof -
  let ?K = "curriculum_scale k"
  have K_four: "4 \<le> ?K" by (rule curriculum_scale_at_least_four)
  have twice_tail_less_population: "2 * ?K^5 < ?K^6"
  proof -
    have K_positive: "0 < ?K^5" using K_four by simp
    have strict_product: "2 * ?K^5 < ?K * ?K^5"
      by (rule mult_strict_right_mono) (use K_four K_positive in simp_all)
    have power_identity: "?K * ?K^5 = ?K^6" by algebra
    show ?thesis using strict_product power_identity by simp
  qed
  show ?thesis
    unfolding curriculum_tail_count_def curriculum_anchor_count_def
      curriculum_population_def
    using twice_tail_less_population by linarith
qed
text \<open>curriculum_counts_even: カリキュラムの個数または母集団分解を整理する。\<close>

lemma curriculum_counts_even:
  "even (curriculum_tail_count k) \<and>
    even (curriculum_anchor_count k)"
  unfolding curriculum_tail_count_def curriculum_anchor_count_def
    curriculum_population_def curriculum_scale_def
  by simp
text \<open>curriculum_tail_ratio_exact: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma curriculum_tail_ratio_exact:
  "curriculum_tail_ratio k = 1 / real (curriculum_scale k)"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  let ?x = "real (curriculum_scale k)"
  have denominator_nonzero:
    "real (curriculum_scale k ^ 6) \<noteq> 0"
    using scale_nonzero by simp
  have cast_five: "real (curriculum_scale k ^ 5) = ?x^5" by simp
  have cast_six: "real (curriculum_scale k ^ 6) = ?x^6" by simp
  have power_split: "?x^6 = ?x * ?x^5" by algebra
  have product_cancel:
    "(1 / ?x) * real (curriculum_scale k ^ 6) =
      real (curriculum_scale k ^ 5)"
  proof -
    have "(1 / ?x) * real (curriculum_scale k ^ 6) =
        (1 / ?x) * (?x * ?x^5)"
      using cast_six power_split by simp
    also have "... = ((1 / ?x) * ?x) * ?x^5" by algebra
    also have "... = ?x^5" using scale_nonzero by simp
    also have "... = real (curriculum_scale k ^ 5)"
      using cast_five by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding curriculum_tail_ratio_def curriculum_tail_count_def
      curriculum_population_def
    by (rule divide_eq_imp[OF denominator_nonzero product_cancel[symmetric]])
qed
text \<open>curriculum_tail_ratio_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_tail_ratio_tendsto_zero:
  "((\<lambda>k. curriculum_tail_ratio k) \<longlongrightarrow> 0) sequentially"
proof -
  have shifted:
    "filterlim (\<lambda>k. (2::real) + real k) at_top sequentially"
    by (rule filterlim_tendsto_add_at_top[OF tendsto_const
          filterlim_real_sequentially])
  have scaled:
    "filterlim (\<lambda>k. (2::real) * (2 + real k)) at_top sequentially"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ shifted]) simp
  have denominator:
    "filterlim (\<lambda>k. real (curriculum_scale k)) at_top sequentially"
    unfolding curriculum_scale_def
    using scaled by (simp add: algebra_simps)
  have inverse_limit:
    "((\<lambda>k. inverse (real (curriculum_scale k)))
      \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_inverse_0_at_top[OF denominator])
  show ?thesis
    using inverse_limit
    by (simp add: curriculum_tail_ratio_exact
          field_class.field_divide_inverse)
qed
text \<open>sigmoid_neg_identity: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma sigmoid_neg_identity:
  "sigmoid (-x) = 1 - sigmoid x"
proof -
  let ?E = "exp x"
  have exponential_positive: "0 < ?E" by (rule exp_gt_zero)
  have exponential_nonzero: "?E \<noteq> 0" using exponential_positive by simp
  have inverse_positive: "0 < inverse ?E"
    by (rule positive_imp_inverse_positive[OF exponential_positive])
  have denominator_nonzero: "1 + ?E \<noteq> 0"
    using exponential_positive by linarith
  have inverse_denominator_nonzero: "1 + inverse ?E \<noteq> 0"
    using inverse_positive by linarith
  have denominator_product: "(1 + inverse ?E) * ?E = 1 + ?E"
  proof -
    have "inverse ?E * ?E = 1" using exponential_nonzero by simp
    then show ?thesis by algebra
  qed
  have ratio_product:
    "(?E / (1 + ?E)) * (1 + inverse ?E) = 1"
  proof -
    have "(?E / (1 + ?E)) * (1 + inverse ?E) =
        ((1 + inverse ?E) * ?E) / (1 + ?E)"
      unfolding field_class.field_divide_inverse by algebra
    also have "... = (1 + ?E) / (1 + ?E)"
      using denominator_product by simp
    also have "... = 1" using denominator_nonzero by simp
    finally show ?thesis .
  qed
  have reciprocal_ratio:
    "1 / (1 + inverse ?E) = ?E / (1 + ?E)"
    by (rule divide_eq_imp[OF inverse_denominator_nonzero ratio_product[symmetric]])
  have ordinary_ratio_product:
    "(?E / (1 + ?E)) * (1 + ?E) = ?E"
    using denominator_nonzero by simp
  have difference_product:
    "(1 - ?E / (1 + ?E)) * (1 + ?E) = 1"
  proof -
    have "(1 - ?E / (1 + ?E)) * (1 + ?E) =
        (1 + ?E) - (?E / (1 + ?E)) * (1 + ?E)"
      by algebra
    also have "... = (1 + ?E) - ?E"
      using ordinary_ratio_product by simp
    also have "... = 1" by algebra
    finally show ?thesis .
  qed
  have reciprocal_difference:
    "1 - ?E / (1 + ?E) = 1 / (1 + ?E)"
    by (rule eq_divide_imp[OF denominator_nonzero difference_product])
  show ?thesis
    unfolding sigmoid_def
    using reciprocal_ratio reciprocal_difference
    by (simp add: exp_minus)
qed
text \<open>sigmoid_lipschitz: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma sigmoid_lipschitz:
  "abs (sigmoid x - sigmoid y) \<le> abs (x - y) / 4"
proof (cases "x \<le> y")
  case True
  have sigmoid_order: "sigmoid x \<le> sigmoid y"
    using sigmoid_difference_bounds(1)[OF True] by linarith
  have upper: "sigmoid y - sigmoid x \<le> (y - x) / 4"
    by (rule sigmoid_difference_bounds(2)[OF True])
  show ?thesis using True sigmoid_order upper
    by simp
next
  case False
  have yx: "y \<le> x" using False by simp
  have sigmoid_order: "sigmoid y \<le> sigmoid x"
    using sigmoid_difference_bounds(1)[OF yx] by linarith
  have upper: "sigmoid x - sigmoid y \<le> (x - y) / 4"
    by (rule sigmoid_difference_bounds(2)[OF yx])
  show ?thesis using yx sigmoid_order upper
    by simp
qed
text \<open>mean_logistic_step_nonexpansive: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma mean_logistic_step_nonexpansive:
  fixes eta q x y :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "abs (mean_logistic_step eta q x - mean_logistic_step eta q y)
    \<le> abs (x - y)"
proof (cases "x \<le> y")
  case True
  note bounds = mean_logistic_step_difference_bounds[OF eta_nonnegative
    eta_at_most_four True, of q]
  show ?thesis using True bounds by simp
next
  case False
  have yx: "y \<le> x" using False by simp
  note bounds = mean_logistic_step_difference_bounds[OF eta_nonnegative
    eta_at_most_four yx, of q]
  show ?thesis using yx bounds by simp
qed
text \<open>signed_bool: ブール値を符号付き実数へ写像する。\<close>

definition signed_bool :: "bool \<Rightarrow> real" where
  "signed_bool b = (if b then 1 else -1)"
text \<open>realizable_feature: 信号とブール属性から二座標特徴を構成する。\<close>

definition realizable_feature :: "real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real \<times> real" where
  "realizable_feature kappa s b =
    (s, kappa * s * signed_bool b)"
text \<open>realizable_score: 二座標重みと特徴の線形スコアを定める。\<close>

definition realizable_score :: "(real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> real" where
  "realizable_score theta x = fst theta * fst x + snd theta * snd x"
text \<open>signed_bool_square: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma signed_bool_square [simp]:
  "signed_bool b ^ 2 = 1"
  unfolding signed_bool_def by (cases b) simp_all
text \<open>realizable_score_witness: スコアから導かれるリスクまたは AUC の値を計算する。\<close>

lemma realizable_score_witness:
  assumes kappa_nonzero: "kappa \<noteq> 0"
  shows "realizable_score (0, 1 / kappa) (realizable_feature kappa s b) =
    clean_label s (signed_bool b)"
  unfolding realizable_score_def realizable_feature_def clean_label_def
  using kappa_nonzero by simp
text \<open>realizable_signed_margin: 更新後の分類マージンを評価する。\<close>

lemma realizable_signed_margin:
  assumes signal_sign: "s = 1 \<or> s = -1"
  shows "clean_label s (signed_bool b) *
      realizable_score (a, beta) (realizable_feature kappa s b) =
    signed_bool b * a + kappa * beta"
  using signal_sign
  unfolding clean_label_def realizable_score_def realizable_feature_def
    signed_bool_def
  by (cases b) auto

primrec realizable_logistic_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "realizable_logistic_state eta kappa xs 0 = (0, 0)"
| "realizable_logistic_state eta kappa xs (Suc k) =
    (let state = realizable_logistic_state eta kappa xs k;
         t = signed_bool (xs ! k);
         response = sigmoid (-(t * fst state + snd state))
     in (fst state + eta * t * response,
         snd state + eta * kappa^2 * response))"
text \<open>realizable_a_state: 実現可能更新の主座標を取り出す。\<close>

definition realizable_a_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "realizable_a_state eta kappa xs k =
    fst (realizable_logistic_state eta kappa xs k)"
text \<open>realizable_u_state: 実現可能更新の補助座標を取り出す。\<close>

definition realizable_u_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "realizable_u_state eta kappa xs k =
    snd (realizable_logistic_state eta kappa xs k)"
text \<open>realizable_states_zero: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma realizable_states_zero [simp]:
  "realizable_a_state eta kappa xs 0 = 0 \<and>
    realizable_u_state eta kappa xs 0 = 0"
  unfolding realizable_a_state_def realizable_u_state_def by simp
text \<open>realizable_a_state_Suc: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma realizable_a_state_Suc:
  "realizable_a_state eta kappa xs (Suc k) =
    realizable_a_state eta kappa xs k +
      eta * signed_bool (xs ! k) *
        sigmoid (-(signed_bool (xs ! k) *
          realizable_a_state eta kappa xs k +
          realizable_u_state eta kappa xs k))"
  unfolding realizable_a_state_def realizable_u_state_def
  by (simp only: realizable_logistic_state.simps Let_def fst_conv snd_conv)
text \<open>realizable_u_state_Suc: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma realizable_u_state_Suc:
  "realizable_u_state eta kappa xs (Suc k) =
    realizable_u_state eta kappa xs k +
      eta * kappa^2 *
        sigmoid (-(signed_bool (xs ! k) *
          realizable_a_state eta kappa xs k +
          realizable_u_state eta kappa xs k))"
  unfolding realizable_a_state_def realizable_u_state_def
  by (simp only: realizable_logistic_state.simps Let_def fst_conv snd_conv)
text \<open>realizable_u_state_bounds: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma realizable_u_state_bounds:
  assumes eta_nonnegative: "0 \<le> eta"
  shows "0 \<le> realizable_u_state eta kappa xs k \<and>
    realizable_u_state eta kappa xs k \<le> real k * eta * kappa^2"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?r = "sigmoid (-(signed_bool (xs ! k) *
    realizable_a_state eta kappa xs k +
    realizable_u_state eta kappa xs k))"
  have response_nonnegative: "0 \<le> ?r"
    using sigmoid_pos[of "-(signed_bool (xs ! k) *
      realizable_a_state eta kappa xs k +
      realizable_u_state eta kappa xs k)"] by linarith
  have response_upper: "?r \<le> 1" by (rule sigmoid_le_one)
  have scale_nonnegative: "0 \<le> eta * kappa^2"
    by (rule mult_nonneg_nonneg[OF eta_nonnegative]) simp
  have increment_nonnegative: "0 \<le> eta * kappa^2 * ?r"
    by (rule mult_nonneg_nonneg[OF scale_nonnegative response_nonnegative])
  have increment_upper: "eta * kappa^2 * ?r \<le> eta * kappa^2"
    using mult_left_mono[OF response_upper, of "eta * kappa^2"]
      scale_nonnegative by simp
  have lower: "0 \<le> realizable_u_state eta kappa xs (Suc k)"
    unfolding realizable_u_state_Suc
    using Suc.IH increment_nonnegative by linarith
  have next_upper:
    "realizable_u_state eta kappa xs k + eta * kappa^2 * ?r \<le>
      real k * eta * kappa^2 + eta * kappa^2"
    using Suc.IH increment_upper by linarith
  have bound_identity:
    "real k * eta * kappa^2 + eta * kappa^2 =
      real (Suc k) * eta * kappa^2"
    by (simp add: algebra_simps)
  have upper: "realizable_u_state eta kappa xs (Suc k) \<le>
      real (Suc k) * eta * kappa^2"
    unfolding realizable_u_state_Suc
    using next_upper bound_identity by linarith
  show ?case using lower upper by blast
qed
text \<open>signed_bool_logistic_increment: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma signed_bool_logistic_increment:
  "signed_bool b * sigmoid (-(signed_bool b * a)) =
    bool_value b - sigmoid a"
  by (cases b)
    (simp_all add: signed_bool_def bool_value_def sigmoid_neg_identity)
text \<open>realizable_increment_difference_bound: 誤差または状態の明示的な上界を与える。\<close>

lemma realizable_increment_difference_bound:
  "abs (signed_bool b * sigmoid (-(signed_bool b * a + u)) -
      (bool_value b - sigmoid a)) \<le> abs u / 4"
proof (cases b)
  case True
  note bound = sigmoid_lipschitz[of "-(a + u)" "-a"]
  show ?thesis using bound True
    by (simp add: signed_bool_def bool_value_def sigmoid_neg_identity)
next
  case False
  note bound = sigmoid_lipschitz[of a "a - u"]
  show ?thesis using bound False
    by (simp add: signed_bool_def bool_value_def)
qed
text \<open>realizable_a_comparison: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma realizable_a_comparison:
  fixes eta kappa q :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "abs (realizable_a_state eta kappa xs k -
      binary_logistic_state eta q xs k) \<le>
    eta^2 * kappa^2 * real k * (real k - 1) / 8"
proof (induction k)
  case 0
  then show ?case
    unfolding binary_logistic_state_def by simp
next
  case (Suc k)
  let ?a = "realizable_a_state eta kappa xs k"
  let ?u = "realizable_u_state eta kappa xs k"
  let ?w = "binary_logistic_state eta q xs k"
  let ?b = "xs ! k"
  let ?d = "signed_bool ?b *
      sigmoid (-(signed_bool ?b * ?a + ?u)) -
      (bool_value ?b - sigmoid ?a)"
  have u_bounds: "0 \<le> ?u \<and> ?u \<le> real k * eta * kappa^2"
    by (rule realizable_u_state_bounds[OF eta_nonnegative])
  have u_nonnegative: "0 \<le> ?u" using u_bounds by blast
  have u_upper: "?u \<le> real k * eta * kappa^2" using u_bounds by blast
  have raw_perturbation: "abs ?d \<le> abs ?u / 4"
    by (rule realizable_increment_difference_bound)
  have perturbation_bound:
    "abs ?d \<le> real k * eta * kappa^2 / 4"
    using raw_perturbation u_nonnegative u_upper by simp
  have a_step:
    "realizable_a_state eta kappa xs (Suc k) =
      mean_logistic_step eta (bool_value ?b) ?a + eta * ?d"
    unfolding realizable_a_state_Suc mean_logistic_step_def
    by algebra
  have w_step:
    "binary_logistic_state eta q xs (Suc k) =
      mean_logistic_step eta (bool_value ?b) ?w"
    unfolding binary_logistic_state_Suc mean_logistic_step_def
    by simp
  have step_difference:
    "realizable_a_state eta kappa xs (Suc k) -
        binary_logistic_state eta q xs (Suc k) =
      (mean_logistic_step eta (bool_value ?b) ?a -
        mean_logistic_step eta (bool_value ?b) ?w) + eta * ?d"
    using a_step w_step by algebra
  have nonexpansive:
    "abs (mean_logistic_step eta (bool_value ?b) ?a -
        mean_logistic_step eta (bool_value ?b) ?w) \<le> abs (?a - ?w)"
    by (rule mean_logistic_step_nonexpansive[OF eta_nonnegative
          eta_at_most_four])
  have scaled_abs: "abs (eta * ?d) = eta * abs ?d"
    using eta_nonnegative by (simp add: abs_mult)
  have triangle:
    "abs ((mean_logistic_step eta (bool_value ?b) ?a -
        mean_logistic_step eta (bool_value ?b) ?w) + eta * ?d) \<le>
      abs (mean_logistic_step eta (bool_value ?b) ?a -
        mean_logistic_step eta (bool_value ?b) ?w) + abs (eta * ?d)"
    by (rule abs_triangle_ineq)
  have transition_bound:
    "abs (realizable_a_state eta kappa xs (Suc k) -
        binary_logistic_state eta q xs (Suc k)) \<le>
      abs (?a - ?w) + eta * abs ?d"
    using step_difference triangle nonexpansive scaled_abs by linarith
  have scaled_perturbation:
    "eta * abs ?d \<le> eta * (real k * eta * kappa^2 / 4)"
    using mult_left_mono[OF perturbation_bound, of eta] eta_nonnegative
    by simp
  have preliminary:
    "abs (realizable_a_state eta kappa xs (Suc k) -
        binary_logistic_state eta q xs (Suc k)) \<le>
      eta^2 * kappa^2 * real k * (real k - 1) / 8 +
        eta * (real k * eta * kappa^2 / 4)"
    using transition_bound Suc.IH scaled_perturbation by linarith
  have bound_identity:
    "eta^2 * kappa^2 * real k * (real k - 1) / 8 +
        eta * (real k * eta * kappa^2 / 4) =
      eta^2 * kappa^2 * real (Suc k) * (real (Suc k) - 1) / 8"
    by (simp add: power2_eq_square field_simps; algebra)
  show ?case using preliminary bound_identity by linarith
qed
text \<open>realizable_transfer_error: 実現可能更新と理想更新の移送誤差を定める。\<close>

definition realizable_transfer_error :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "realizable_transfer_error eta kappa N =
    kappa^2 * (eta * real N +
      eta^2 * real N * (real N - 1) / 8)"
text \<open>signed_bool_abs: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma signed_bool_abs [simp]: "abs (signed_bool b) = 1"
  unfolding signed_bool_def by (cases b) simp_all
text \<open>realizable_u_state_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma realizable_u_state_positive:
  assumes eta_positive: "0 < eta"
    and kappa_nonzero: "kappa \<noteq> 0"
    and N_positive: "0 < N"
  shows "0 < realizable_u_state eta kappa xs N"
proof -
  obtain k where N: "N = Suc k" using N_positive by (cases N) auto
  have previous_bounds:
    "0 \<le> realizable_u_state eta kappa xs k \<and>
      realizable_u_state eta kappa xs k \<le> real k * eta * kappa^2"
    by (rule realizable_u_state_bounds[OF order_less_imp_le[OF eta_positive]])
  have previous_nonnegative:
    "0 \<le> realizable_u_state eta kappa xs k"
    using previous_bounds by blast
  have scale_positive: "0 < eta * kappa^2"
    using eta_positive kappa_nonzero by (intro mult_pos_pos) simp_all
  have response_positive:
    "0 < sigmoid (-(signed_bool (xs ! k) *
      realizable_a_state eta kappa xs k +
      realizable_u_state eta kappa xs k))"
    by (rule sigmoid_pos)
  have increment_positive:
    "0 < eta * kappa^2 * sigmoid (-(signed_bool (xs ! k) *
      realizable_a_state eta kappa xs k +
      realizable_u_state eta kappa xs k))"
    by (rule mult_pos_pos[OF scale_positive response_positive])
  show ?thesis
    unfolding N realizable_u_state_Suc
    using previous_nonnegative increment_positive by linarith
qed
text \<open>realizable_margin_comparison: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma realizable_margin_comparison:
  fixes eta kappa q :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "abs (signed_bool b * realizable_a_state eta kappa xs N +
      realizable_u_state eta kappa xs N -
      signed_bool b * binary_logistic_state eta q xs N) \<le>
    realizable_transfer_error eta kappa N"
proof -
  let ?a = "realizable_a_state eta kappa xs N"
  let ?u = "realizable_u_state eta kappa xs N"
  let ?w = "binary_logistic_state eta q xs N"
  have a_bound: "abs (?a - ?w) \<le>
      eta^2 * kappa^2 * real N * (real N - 1) / 8"
    by (rule realizable_a_comparison[OF eta_nonnegative eta_at_most_four])
  have u_bounds: "0 \<le> ?u \<and> ?u \<le> real N * eta * kappa^2"
    by (rule realizable_u_state_bounds[OF eta_nonnegative])
  have difference_identity:
    "signed_bool b * ?a + ?u - signed_bool b * ?w =
      signed_bool b * (?a - ?w) + ?u"
    by algebra
  have triangle:
    "abs (signed_bool b * (?a - ?w) + ?u) \<le>
      abs (signed_bool b * (?a - ?w)) + abs ?u"
    by (rule abs_triangle_ineq)
  have factor_abs: "abs (signed_bool b * (?a - ?w)) = abs (?a - ?w)"
    by (simp add: abs_mult)
  have combined:
    "abs (signed_bool b * ?a + ?u - signed_bool b * ?w) \<le>
      eta^2 * kappa^2 * real N * (real N - 1) / 8 +
        real N * eta * kappa^2"
    using difference_identity triangle factor_abs a_bound u_bounds by linarith
  have error_identity:
    "eta^2 * kappa^2 * real N * (real N - 1) / 8 +
        real N * eta * kappa^2 =
      realizable_transfer_error eta kappa N"
    unfolding realizable_transfer_error_def
    by (simp add: power2_eq_square field_simps; algebra)
  show ?thesis using combined error_identity by linarith
qed
text \<open>realizable_positive_dominance_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma realizable_positive_dominance_transfer:
  fixes eta kappa q G :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and reference_margin: "G \<le> binary_logistic_state eta q xs N"
    and error_small: "realizable_transfer_error eta kappa N < G"
  shows "realizable_u_state eta kappa xs N <
    realizable_a_state eta kappa xs N"
proof -
  have comparison:
    "abs (-realizable_a_state eta kappa xs N +
        realizable_u_state eta kappa xs N +
        binary_logistic_state eta q xs N) \<le>
      realizable_transfer_error eta kappa N"
    using realizable_margin_comparison[OF eta_nonnegative eta_at_most_four,
      where b=False and xs=xs and N=N and q=q and kappa=kappa]
    by (simp add: signed_bool_def)
  have self_upper:
    "-realizable_a_state eta kappa xs N +
        realizable_u_state eta kappa xs N +
        binary_logistic_state eta q xs N \<le>
      realizable_transfer_error eta kappa N"
    using comparison abs_ge_self by linarith
  show ?thesis using self_upper reference_margin error_small by linarith
qed
text \<open>realizable_negative_dominance_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma realizable_negative_dominance_transfer:
  fixes eta kappa q G :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and reference_margin: "binary_logistic_state eta q xs N \<le> -G"
    and error_small: "realizable_transfer_error eta kappa N < G"
  shows "realizable_a_state eta kappa xs N <
    -realizable_u_state eta kappa xs N"
proof -
  have comparison:
    "abs (realizable_a_state eta kappa xs N +
        realizable_u_state eta kappa xs N -
        binary_logistic_state eta q xs N) \<le>
      realizable_transfer_error eta kappa N"
    using realizable_margin_comparison[OF eta_nonnegative eta_at_most_four,
      where b=True and xs=xs and N=N and q=q and kappa=kappa]
    by (simp add: signed_bool_def)
  have self_upper:
    "realizable_a_state eta kappa xs N +
        realizable_u_state eta kappa xs N -
        binary_logistic_state eta q xs N \<le>
      realizable_transfer_error eta kappa N"
    using comparison abs_ge_self by linarith
  show ?thesis using self_upper reference_margin error_small by linarith
qed
text \<open>realizable_test_risk: 二座標実現可能モデルのテストリスクを定める。\<close>

definition realizable_test_risk :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "realizable_test_risk epsilon a u =
    (1 - epsilon) * zero_one_margin_loss (a + u) +
      epsilon * zero_one_margin_loss (-a + u)"
text \<open>realizable_test_risk_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma realizable_test_risk_positive:
  assumes u_positive: "0 < u" and dominant_positive: "u < a"
  shows "realizable_test_risk epsilon a u = epsilon"
  unfolding realizable_test_risk_def zero_one_margin_loss_def
  using u_positive dominant_positive by simp
text \<open>realizable_test_risk_negative: 対象量が負であること、または負側の評価を示す。\<close>

lemma realizable_test_risk_negative:
  assumes u_positive: "0 < u" and dominant_negative: "a < -u"
  shows "realizable_test_risk epsilon a u = 1 - epsilon"
  unfolding realizable_test_risk_def zero_one_margin_loss_def
  using u_positive dominant_negative by simp
text \<open>realizable_inversion_transfer: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem realizable_inversion_transfer:
  fixes eta kappa q G_attack G_random epsilon :: real
  assumes eta_positive: "0 < eta"
    and eta_at_most_four: "eta \<le> 4"
    and kappa_nonzero: "kappa \<noteq> 0"
    and N_positive: "0 < N"
    and attack_reference:
      "binary_logistic_state eta q xs_attack N \<le> -G_attack"
    and random_reference:
      "G_random \<le> binary_logistic_state eta q xs_random N"
    and error_small:
      "realizable_transfer_error eta kappa N < min G_attack G_random"
  shows "realizable_test_risk epsilon
        (realizable_a_state eta kappa xs_attack N)
        (realizable_u_state eta kappa xs_attack N) = 1 - epsilon \<and>
    realizable_test_risk epsilon
        (realizable_a_state eta kappa xs_random N)
        (realizable_u_state eta kappa xs_random N) = epsilon \<and>
    realizable_test_auc epsilon
        (realizable_a_state eta kappa xs_attack N)
        (realizable_u_state eta kappa xs_attack N) =
      2 * epsilon - epsilon^2 \<and>
    realizable_test_auc epsilon
        (realizable_a_state eta kappa xs_random N)
        (realizable_u_state eta kappa xs_random N) =
      1 - epsilon^2"
proof -
  have eta_nonnegative: "0 \<le> eta" using eta_positive by linarith
  have attack_error:
    "realizable_transfer_error eta kappa N < G_attack"
    using error_small by simp
  have random_error:
    "realizable_transfer_error eta kappa N < G_random"
    using error_small by simp
  have attack_u_positive:
    "0 < realizable_u_state eta kappa xs_attack N"
    by (rule realizable_u_state_positive[OF eta_positive kappa_nonzero N_positive])
  have random_u_positive:
    "0 < realizable_u_state eta kappa xs_random N"
    by (rule realizable_u_state_positive[OF eta_positive kappa_nonzero N_positive])
  have attack_dominance:
    "realizable_a_state eta kappa xs_attack N <
      -realizable_u_state eta kappa xs_attack N"
    by (rule realizable_negative_dominance_transfer[OF eta_nonnegative
          eta_at_most_four attack_reference attack_error])
  have random_dominance:
    "realizable_u_state eta kappa xs_random N <
      realizable_a_state eta kappa xs_random N"
    by (rule realizable_positive_dominance_transfer[OF eta_nonnegative
          eta_at_most_four random_reference random_error])
  have attack_risk:
    "realizable_test_risk epsilon
        (realizable_a_state eta kappa xs_attack N)
        (realizable_u_state eta kappa xs_attack N) = 1 - epsilon"
    by (rule realizable_test_risk_negative[OF attack_u_positive attack_dominance])
  have random_risk:
    "realizable_test_risk epsilon
        (realizable_a_state eta kappa xs_random N)
        (realizable_u_state eta kappa xs_random N) = epsilon"
    by (rule realizable_test_risk_positive[OF random_u_positive random_dominance])
  have attack_auc:
    "realizable_test_auc epsilon
        (realizable_a_state eta kappa xs_attack N)
        (realizable_u_state eta kappa xs_attack N) =
      2 * epsilon - epsilon^2"
    by (rule realizable_test_auc_attack[OF attack_u_positive attack_dominance])
  have random_auc:
    "realizable_test_auc epsilon
        (realizable_a_state eta kappa xs_random N)
        (realizable_u_state eta kappa xs_random N) =
      1 - epsilon^2"
    by (rule realizable_test_auc_random[OF random_u_positive random_dominance])
  show ?thesis using attack_risk random_risk attack_auc random_auc by blast
qed
text \<open>realizable_random_metric_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

theorem realizable_random_metric_transfer:
  fixes eta kappa q epsilon :: real
  assumes eta_positive: "0 < eta"
    and eta_at_most_four: "eta \<le> 4"
    and kappa_nonzero: "kappa \<noteq> 0"
    and N_positive: "0 < N"
    and reference_margin: "1 \<le> binary_logistic_state eta q xs N"
    and error_small: "realizable_transfer_error eta kappa N < 1"
  shows "realizable_test_risk epsilon
      (realizable_a_state eta kappa xs N)
      (realizable_u_state eta kappa xs N) = epsilon"
    and "realizable_test_auc epsilon
      (realizable_a_state eta kappa xs N)
      (realizable_u_state eta kappa xs N) = 1 - epsilon^2"
proof -
  have eta_nonnegative: "0 \<le> eta"
    using eta_positive by linarith
  have u_positive: "0 < realizable_u_state eta kappa xs N"
    by (rule realizable_u_state_positive[OF eta_positive kappa_nonzero N_positive])
  have dominance:
    "realizable_u_state eta kappa xs N < realizable_a_state eta kappa xs N"
    by (rule realizable_positive_dominance_transfer
        [OF eta_nonnegative eta_at_most_four reference_margin error_small])
  show "realizable_test_risk epsilon
      (realizable_a_state eta kappa xs N)
      (realizable_u_state eta kappa xs N) = epsilon"
    by (rule realizable_test_risk_positive[OF u_positive dominance])
  show "realizable_test_auc epsilon
      (realizable_a_state eta kappa xs N)
      (realizable_u_state eta kappa xs N) = 1 - epsilon^2"
    by (rule realizable_test_auc_random[OF u_positive dominance])
qed

primrec momentum_logistic_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "momentum_logistic_state eta mu xs 0 = (0, 0)"
| "momentum_logistic_state eta mu xs (Suc k) =
    (let state = momentum_logistic_state eta mu xs k;
         gradient = sigmoid (fst state) - bool_value (xs ! k);
         velocity = mu * snd state + gradient
     in (fst state - eta * velocity, velocity))"
text \<open>momentum_w_state: モメンタム更新の重み座標を取り出す。\<close>

definition momentum_w_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_w_state eta mu xs k =
    fst (momentum_logistic_state eta mu xs k)"
text \<open>momentum_v_state: モメンタム更新の速度座標を取り出す。\<close>

definition momentum_v_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_v_state eta mu xs k =
    snd (momentum_logistic_state eta mu xs k)"
text \<open>momentum_effective_step: モメンタムを含む有効学習ステップを定める。\<close>

definition momentum_effective_step :: "real \<Rightarrow> real \<Rightarrow> real" where
  "momentum_effective_step eta mu = eta / (1 - mu)"
text \<open>momentum_z_state: モメンタム状態を有効更新との差として定める。\<close>

definition momentum_z_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_z_state eta mu xs k =
    momentum_w_state eta mu xs k -
      momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k"
text \<open>momentum_states_zero: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma momentum_states_zero [simp]:
  "momentum_w_state eta mu xs 0 = 0 \<and>
    momentum_v_state eta mu xs 0 = 0 \<and>
    momentum_z_state eta mu xs 0 = 0"
  unfolding momentum_w_state_def momentum_v_state_def momentum_z_state_def
  by simp
text \<open>momentum_v_state_Suc: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma momentum_v_state_Suc:
  "momentum_v_state eta mu xs (Suc k) =
    mu * momentum_v_state eta mu xs k +
      (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k))"
  unfolding momentum_v_state_def momentum_w_state_def
  by (simp only: momentum_logistic_state.simps Let_def fst_conv snd_conv)
text \<open>momentum_w_state_Suc: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma momentum_w_state_Suc:
  "momentum_w_state eta mu xs (Suc k) =
    momentum_w_state eta mu xs k - eta *
      (mu * momentum_v_state eta mu xs k +
        (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k)))"
  unfolding momentum_v_state_def momentum_w_state_def
  by (simp only: momentum_logistic_state.simps Let_def fst_conv snd_conv)
text \<open>momentum_z_state_Suc: 状態更新の初期値、再帰式、または明示式を示す。\<close>

lemma momentum_z_state_Suc:
  assumes mu_not_one: "mu \<noteq> 1"
  shows "momentum_z_state eta mu xs (Suc k) =
    momentum_z_state eta mu xs k +
      momentum_effective_step eta mu *
        (bool_value (xs ! k) - sigmoid (momentum_w_state eta mu xs k))"
proof -
  have denominator_nonzero: "1 - mu \<noteq> 0" using mu_not_one by linarith
  have effective_balance:
    "momentum_effective_step eta mu * (1 - mu) = eta"
    unfolding momentum_effective_step_def
    using denominator_nonzero by simp
  have eta_identity:
    "eta = momentum_effective_step eta mu * (1 - mu)"
    using effective_balance by simp
  have transform_algebra:
    "w - eta * (mu * v + g) - h * mu * (mu * v + g) =
      w - h * mu * v - h * g"
    if relation: "eta = h * (1 - mu)" for h w v g
  proof -
    have "w - eta * (mu * v + g) - h * mu * (mu * v + g) =
      w - (h * (1 - mu)) * (mu * v + g) - h * mu * (mu * v + g)"
      using relation by simp
    also have "\<dots> = w - h * mu * v - h * g" by algebra
    finally show ?thesis .
  qed
  have transformed:
    "momentum_w_state eta mu xs k -
        eta * (mu * momentum_v_state eta mu xs k +
          (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k))) -
        momentum_effective_step eta mu * mu *
          (mu * momentum_v_state eta mu xs k +
            (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k))) =
      momentum_w_state eta mu xs k -
        momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k -
        momentum_effective_step eta mu *
          (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k))"
    by (rule transform_algebra[OF eta_identity])
  have rhs_identity:
    "momentum_w_state eta mu xs k -
        momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k -
        momentum_effective_step eta mu *
          (sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k)) =
      momentum_w_state eta mu xs k -
        momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k +
        momentum_effective_step eta mu *
          (bool_value (xs ! k) - sigmoid (momentum_w_state eta mu xs k))"
    by algebra
  show ?thesis
    unfolding momentum_z_state_def momentum_w_state_Suc momentum_v_state_Suc
    using transformed rhs_identity by simp
qed
text \<open>binary_logistic_gradient_abs_le_one: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma binary_logistic_gradient_abs_le_one:
  "abs (sigmoid w - bool_value b) \<le> 1"
proof (cases b)
  case False
  have sigmoid_positive: "0 < sigmoid w" by (rule sigmoid_pos)
  have sigmoid_nonnegative: "0 \<le> sigmoid w" using sigmoid_positive by linarith
  have sigmoid_upper: "sigmoid w \<le> 1" by (rule sigmoid_le_one)
  have difference: "sigmoid w - bool_value False = sigmoid w"
    by (simp add: bool_value_def)
  have absolute: "abs (sigmoid w - bool_value False) = sigmoid w"
  proof -
    have "abs (sigmoid w - bool_value False) = abs (sigmoid w)"
      using difference by simp
    also have "\<dots> = sigmoid w" by (rule abs_of_nonneg[OF sigmoid_nonnegative])
    finally show ?thesis .
  qed
  have target: "abs (sigmoid w - bool_value False) \<le> 1"
    using absolute sigmoid_upper by simp
  show ?thesis using False target by simp
next
  case True
  have sigmoid_positive: "0 < sigmoid w" by (rule sigmoid_pos)
  have sigmoid_upper: "sigmoid w \<le> 1" by (rule sigmoid_le_one)
  have difference_nonpositive: "sigmoid w - 1 \<le> 0"
    using sigmoid_upper by linarith
  have difference: "sigmoid w - bool_value True = sigmoid w - 1"
    by (simp add: bool_value_def)
  have absolute: "abs (sigmoid w - bool_value True) = 1 - sigmoid w"
  proof -
    have "abs (sigmoid w - bool_value True) = abs (sigmoid w - 1)"
      using difference by simp
    also have "\<dots> = - (sigmoid w - 1)"
      by (rule abs_of_nonpos[OF difference_nonpositive])
    also have "\<dots> = 1 - sigmoid w" by algebra
    finally show ?thesis .
  qed
  have target: "abs (sigmoid w - bool_value True) \<le> 1"
    using absolute sigmoid_positive by linarith
  show ?thesis using True target by simp
qed
text \<open>momentum_velocity_bound: 誤差または状態の明示的な上界を与える。\<close>

lemma momentum_velocity_bound:
  assumes mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
  shows "abs (momentum_v_state eta mu xs k) \<le> 1 / (1 - mu)"
proof (induction k)
  case 0
  have denominator_positive: "0 < 1 - mu" using mu_less_one by linarith
  have "0 < 1 / (1 - mu)" using denominator_positive by simp
  then show ?case by simp
next
  case (Suc k)
  let ?v = "momentum_v_state eta mu xs k"
  let ?g = "sigmoid (momentum_w_state eta mu xs k) - bool_value (xs ! k)"
  have gradient_bound: "abs ?g \<le> 1"
    by (rule binary_logistic_gradient_abs_le_one)
  have mu_absolute: "abs mu = mu"
    unfolding abs_of_nonneg[OF mu_nonnegative] by simp
  have step_bound: "abs (mu * ?v + ?g) \<le> mu * abs ?v + abs ?g"
  proof -
    have "abs (mu * ?v + ?g) \<le> abs (mu * ?v) + abs ?g"
      by (rule abs_triangle_ineq)
    also have "\<dots> = mu * abs ?v + abs ?g"
      unfolding abs_mult mu_absolute by simp
    finally show ?thesis .
  qed
  have scaled_induction:
    "mu * abs ?v \<le> mu * (1 / (1 - mu))"
    by (rule mult_left_mono[OF Suc.IH mu_nonnegative])
  have denominator_nonzero: "1 - mu \<noteq> 0" using mu_less_one by linarith
  have fixed_point:
    "mu * (1 / (1 - mu)) + 1 = 1 / (1 - mu)"
    using denominator_nonzero by (simp add: field_simps; algebra)
  show ?case
    unfolding momentum_v_state_Suc
    using step_bound gradient_bound scaled_induction fixed_point by linarith
qed
text \<open>momentum_transform_error: モメンタム変換に伴う一段誤差を定める。\<close>

definition momentum_transform_error :: "real \<Rightarrow> real \<Rightarrow> real" where
  "momentum_transform_error eta mu = eta * mu / (1 - mu)^2"
text \<open>momentum_transform_error_nonnegative: 誤差または状態の明示的な上界を与える。\<close>

lemma momentum_transform_error_nonnegative:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
  shows "0 \<le> momentum_transform_error eta mu"
proof -
  have denominator_positive: "0 < (1 - mu)^2" using mu_less_one by simp
  have numerator_nonnegative: "0 \<le> eta * mu"
    using eta_nonnegative mu_nonnegative by (rule mult_nonneg_nonneg)
  show ?thesis
    unfolding momentum_transform_error_def
    using numerator_nonnegative denominator_positive by simp
qed
text \<open>momentum_transform_gap_bound: 誤差または状態の明示的な上界を与える。\<close>

lemma momentum_transform_gap_bound:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
  shows "abs (momentum_z_state eta mu xs k - momentum_w_state eta mu xs k) \<le>
    momentum_transform_error eta mu"
proof -
  have denominator_positive: "0 < 1 - mu" using mu_less_one by linarith
  have denominator_nonzero: "1 - mu \<noteq> 0" using denominator_positive by linarith
  have effective_nonnegative: "0 \<le> momentum_effective_step eta mu"
    unfolding momentum_effective_step_def
    using eta_nonnegative denominator_positive by simp
  have effective_absolute:
    "abs (momentum_effective_step eta mu) = momentum_effective_step eta mu"
    unfolding abs_of_nonneg[OF effective_nonnegative] by simp
  have mu_absolute: "abs mu = mu"
    unfolding abs_of_nonneg[OF mu_nonnegative] by simp
  have difference_identity:
    "momentum_z_state eta mu xs k - momentum_w_state eta mu xs k =
      - (momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k)"
    unfolding momentum_z_state_def by algebra
  have gap_identity:
    "abs (momentum_z_state eta mu xs k - momentum_w_state eta mu xs k) =
      momentum_effective_step eta mu * mu * abs (momentum_v_state eta mu xs k)"
  proof -
    have "abs (momentum_z_state eta mu xs k - momentum_w_state eta mu xs k) =
      abs (momentum_effective_step eta mu * mu * momentum_v_state eta mu xs k)"
      using difference_identity by simp
    also have "\<dots> = abs (momentum_effective_step eta mu) * abs mu *
      abs (momentum_v_state eta mu xs k)"
      by (simp only: abs_mult)
    also have "\<dots> = momentum_effective_step eta mu * mu *
      abs (momentum_v_state eta mu xs k)"
      unfolding effective_absolute mu_absolute by simp
    finally show ?thesis .
  qed
  have velocity_bound:
    "abs (momentum_v_state eta mu xs k) \<le> 1 / (1 - mu)"
    by (rule momentum_velocity_bound[OF mu_nonnegative mu_less_one])
  have coefficient_nonnegative:
    "0 \<le> momentum_effective_step eta mu * mu"
    using effective_nonnegative mu_nonnegative by (rule mult_nonneg_nonneg)
  have product_bound:
    "momentum_effective_step eta mu * mu * abs (momentum_v_state eta mu xs k) \<le>
      momentum_effective_step eta mu * mu * (1 / (1 - mu))"
    by (rule mult_left_mono[OF velocity_bound coefficient_nonnegative])
  have coefficient_identity:
    "momentum_effective_step eta mu * mu * (1 / (1 - mu)) =
      momentum_transform_error eta mu"
    unfolding momentum_effective_step_def momentum_transform_error_def
    using denominator_nonzero by (simp add: power2_eq_square field_simps; algebra)
  have "abs (momentum_z_state eta mu xs k - momentum_w_state eta mu xs k) =
    momentum_effective_step eta mu * mu * abs (momentum_v_state eta mu xs k)"
    by (rule gap_identity)
  also have "\<dots> \<le> momentum_effective_step eta mu * mu * (1 / (1 - mu))"
    by (rule product_bound)
  also have "\<dots> = momentum_transform_error eta mu"
    by (rule coefficient_identity)
  finally show ?thesis .
qed
text \<open>momentum_z_comparison: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma momentum_z_comparison:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
  shows "abs (momentum_z_state eta mu xs N -
      binary_logistic_state (momentum_effective_step eta mu) q xs N) \<le>
    real N * momentum_effective_step eta mu *
      momentum_transform_error eta mu / 4"
proof (induction N)
  case 0
  show ?case by (simp add: binary_logistic_state_def)
next
  case (Suc k)
  let ?h = "momentum_effective_step eta mu"
  let ?D = "momentum_transform_error eta mu"
  let ?z = "momentum_z_state eta mu xs k"
  let ?w = "momentum_w_state eta mu xs k"
  let ?reference = "binary_logistic_state ?h q xs k"
  have denominator_positive: "0 < 1 - mu" using mu_less_one by linarith
  have mu_not_one: "mu \<noteq> 1" using mu_less_one by linarith
  have effective_nonnegative: "0 \<le> ?h"
    unfolding momentum_effective_step_def
    using eta_nonnegative denominator_positive by simp
  have effective_absolute: "abs ?h = ?h"
    by (rule abs_of_nonneg[OF effective_nonnegative])
  have z_recurrence:
    "momentum_z_state eta mu xs (Suc k) =
      ?z + ?h * (bool_value (xs ! k) - sigmoid ?w)"
    by (rule momentum_z_state_Suc[OF mu_not_one])
  have reference_recurrence:
    "binary_logistic_state ?h q xs (Suc k) =
      ?reference + ?h * (bool_value (xs ! k) - sigmoid ?reference)"
    by (rule binary_logistic_state_Suc)
  have difference_identity:
    "momentum_z_state eta mu xs (Suc k) -
        binary_logistic_state ?h q xs (Suc k) =
      (mean_logistic_step ?h q ?z - mean_logistic_step ?h q ?reference) +
        ?h * (sigmoid ?z - sigmoid ?w)"
    unfolding z_recurrence reference_recurrence mean_logistic_step_def
    by algebra
  have nonexpansive:
    "abs (mean_logistic_step ?h q ?z - mean_logistic_step ?h q ?reference) \<le>
      abs (?z - ?reference)"
    by (rule mean_logistic_step_nonexpansive[OF effective_nonnegative
          effective_at_most_four])
  have sigmoid_gap:
    "abs (sigmoid ?z - sigmoid ?w) \<le> ?D / 4"
  proof -
    have lipschitz: "abs (sigmoid ?z - sigmoid ?w) \<le> abs (?z - ?w) / 4"
      by (rule sigmoid_lipschitz)
    have transform_gap: "abs (?z - ?w) \<le> ?D"
      by (rule momentum_transform_gap_bound[OF eta_nonnegative mu_nonnegative
            mu_less_one])
    have quarter_nonnegative: "0 \<le> (1 / 4 :: real)" by simp
    have multiplied_gap:
      "(1 / 4) * abs (?z - ?w) \<le> (1 / 4) * ?D"
      by (rule mult_left_mono[OF transform_gap quarter_nonnegative])
    have divided_gap: "abs (?z - ?w) / 4 \<le> ?D / 4"
      using multiplied_gap by simp
    have "abs (sigmoid ?z - sigmoid ?w) \<le> abs (?z - ?w) / 4"
      by (rule lipschitz)
    also have "\<dots> \<le> ?D / 4" by (rule divided_gap)
    finally show ?thesis .
  qed
  have scaled_sigmoid_gap:
    "abs (?h * (sigmoid ?z - sigmoid ?w)) \<le> ?h * (?D / 4)"
  proof -
    have absolute_identity:
      "abs (?h * (sigmoid ?z - sigmoid ?w)) =
        ?h * abs (sigmoid ?z - sigmoid ?w)"
      unfolding abs_mult effective_absolute by simp
    have product_bound:
      "?h * abs (sigmoid ?z - sigmoid ?w) \<le> ?h * (?D / 4)"
      by (rule mult_left_mono[OF sigmoid_gap effective_nonnegative])
    show ?thesis using absolute_identity product_bound by simp
  qed
  have step_bound:
    "abs (momentum_z_state eta mu xs (Suc k) -
        binary_logistic_state ?h q xs (Suc k)) \<le>
      abs (?z - ?reference) + ?h * (?D / 4)"
  proof -
    have "abs (momentum_z_state eta mu xs (Suc k) -
        binary_logistic_state ?h q xs (Suc k)) =
      abs ((mean_logistic_step ?h q ?z - mean_logistic_step ?h q ?reference) +
        ?h * (sigmoid ?z - sigmoid ?w))"
      using difference_identity by simp
    also have "\<dots> \<le>
        abs (mean_logistic_step ?h q ?z - mean_logistic_step ?h q ?reference) +
        abs (?h * (sigmoid ?z - sigmoid ?w))"
      by (rule abs_triangle_ineq)
    finally have triangle_bound:
      "abs (momentum_z_state eta mu xs (Suc k) -
          binary_logistic_state ?h q xs (Suc k)) \<le>
        abs (mean_logistic_step ?h q ?z - mean_logistic_step ?h q ?reference) +
          abs (?h * (sigmoid ?z - sigmoid ?w))" .
    show ?thesis using triangle_bound nonexpansive scaled_sigmoid_gap by linarith
  qed
  have arithmetic_identity:
    "real k * ?h * ?D / 4 + ?h * (?D / 4) =
      real (Suc k) * ?h * ?D / 4"
    by (simp; algebra)
  show ?case using step_bound Suc.IH arithmetic_identity by linarith
qed
text \<open>momentum_transfer_error: モメンタム更新を理想更新へ移送する誤差予算を定める。\<close>

definition momentum_transfer_error :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "momentum_transfer_error eta mu N =
    momentum_transform_error eta mu *
      (1 + real N * momentum_effective_step eta mu / 4)"
text \<open>momentum_state_comparison: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma momentum_state_comparison:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
  shows "abs (momentum_w_state eta mu xs N -
      binary_logistic_state (momentum_effective_step eta mu) q xs N) \<le>
    momentum_transfer_error eta mu N"
proof -
  let ?h = "momentum_effective_step eta mu"
  let ?D = "momentum_transform_error eta mu"
  let ?w = "momentum_w_state eta mu xs N"
  let ?z = "momentum_z_state eta mu xs N"
  let ?reference = "binary_logistic_state ?h q xs N"
  have transform_gap: "abs (?z - ?w) \<le> ?D"
    by (rule momentum_transform_gap_bound[OF eta_nonnegative mu_nonnegative
          mu_less_one])
  have reverse_transform_gap: "abs (?w - ?z) \<le> ?D"
  proof -
    have "abs (?w - ?z) = abs (?z - ?w)"
      by (simp add: abs_minus_commute)
    also have "\<dots> \<le> ?D" by (rule transform_gap)
    finally show ?thesis .
  qed
  have transformed_comparison: "abs (?z - ?reference) \<le> real N * ?h * ?D / 4"
    by (rule momentum_z_comparison[OF eta_nonnegative mu_nonnegative
          mu_less_one effective_at_most_four])
  have triangle:
    "abs (?w - ?reference) \<le> abs (?w - ?z) + abs (?z - ?reference)"
  proof -
    have difference_identity: "?w - ?reference = (?w - ?z) + (?z - ?reference)"
      by algebra
    have "abs (?w - ?reference) = abs ((?w - ?z) + (?z - ?reference))"
      using difference_identity by simp
    also have "\<dots> \<le> abs (?w - ?z) + abs (?z - ?reference)"
      by (rule abs_triangle_ineq)
    finally show ?thesis .
  qed
  have combined:
    "abs (?w - ?reference) \<le> ?D + real N * ?h * ?D / 4"
    using triangle reverse_transform_gap transformed_comparison by linarith
  have error_identity:
    "?D + real N * ?h * ?D / 4 = momentum_transfer_error eta mu N"
    unfolding momentum_transfer_error_def by algebra
  show ?thesis using combined error_identity by linarith
qed
text \<open>momentum_positive_margin_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma momentum_positive_margin_transfer:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
    and reference_margin:
      "G \<le> binary_logistic_state (momentum_effective_step eta mu) q xs N"
    and error_small: "momentum_transfer_error eta mu N < G"
  shows "0 < momentum_w_state eta mu xs N"
proof -
  let ?w = "momentum_w_state eta mu xs N"
  let ?reference =
    "binary_logistic_state (momentum_effective_step eta mu) q xs N"
  have comparison: "abs (?w - ?reference) \<le> momentum_transfer_error eta mu N"
    by (rule momentum_state_comparison[OF eta_nonnegative mu_nonnegative
          mu_less_one effective_at_most_four])
  have reverse_difference:
    "?reference - ?w \<le> momentum_transfer_error eta mu N"
    using comparison abs_ge_minus_self[of "?w - ?reference"] by linarith
  show ?thesis using reverse_difference reference_margin error_small by linarith
qed
text \<open>momentum_negative_margin_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma momentum_negative_margin_transfer:
  assumes eta_nonnegative: "0 \<le> eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
    and reference_margin:
      "binary_logistic_state (momentum_effective_step eta mu) q xs N \<le> -G"
    and error_small: "momentum_transfer_error eta mu N < G"
  shows "momentum_w_state eta mu xs N < 0"
proof -
  let ?w = "momentum_w_state eta mu xs N"
  let ?reference =
    "binary_logistic_state (momentum_effective_step eta mu) q xs N"
  have comparison: "abs (?w - ?reference) \<le> momentum_transfer_error eta mu N"
    by (rule momentum_state_comparison[OF eta_nonnegative mu_nonnegative
          mu_less_one effective_at_most_four])
  have forward_difference:
    "?w - ?reference \<le> momentum_transfer_error eta mu N"
    using comparison abs_ge_self[of "?w - ?reference"] by linarith
  show ?thesis using forward_difference reference_margin error_small by linarith
qed
text \<open>momentum_zero_reference_exact: 対象量の厳密な閉形式を示す。\<close>

lemma momentum_zero_reference_exact:
  assumes eta_nonnegative: "0 \<le> eta" and eta_at_most_four: "eta \<le> 4"
  shows "momentum_w_state eta 0 xs N = binary_logistic_state eta q xs N"
proof -
  have comparison:
    "abs (momentum_w_state eta 0 xs N -
      binary_logistic_state (momentum_effective_step eta 0) q xs N) \<le>
      momentum_transfer_error eta 0 N"
    apply (rule momentum_state_comparison)
    apply (rule eta_nonnegative)
    apply simp
    apply simp
    using eta_at_most_four
    apply (simp add: momentum_effective_step_def)
    done
  show ?thesis
    using comparison
    unfolding momentum_effective_step_def momentum_transfer_error_def
      momentum_transform_error_def
    by simp
qed
text \<open>momentum_inversion_transfer: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem momentum_inversion_transfer:
  fixes eta mu q G_attack G_random epsilon :: real
  assumes eta_positive: "0 < eta"
    and mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and effective_at_most_four: "momentum_effective_step eta mu \<le> 4"
    and attack_reference:
      "binary_logistic_state (momentum_effective_step eta mu) q xs_attack N \<le>
        -G_attack"
    and random_reference:
      "G_random \<le>
        binary_logistic_state (momentum_effective_step eta mu) q xs_random N"
    and error_small:
      "momentum_transfer_error eta mu N < min G_attack G_random"
  shows "clean_test_risk epsilon (momentum_w_state eta mu xs_attack N) =
        1 - epsilon \<and>
    clean_test_risk epsilon (momentum_w_state eta mu xs_random N) = epsilon \<and>
    clean_test_auc epsilon (momentum_w_state eta mu xs_attack N) = epsilon \<and>
    clean_test_auc epsilon (momentum_w_state eta mu xs_random N) = 1 - epsilon"
proof -
  have eta_nonnegative: "0 \<le> eta" using eta_positive by linarith
  have attack_error: "momentum_transfer_error eta mu N < G_attack"
    using error_small by simp
  have random_error: "momentum_transfer_error eta mu N < G_random"
    using error_small by simp
  have attack_negative: "momentum_w_state eta mu xs_attack N < 0"
    by (rule momentum_negative_margin_transfer[OF eta_nonnegative mu_nonnegative
          mu_less_one effective_at_most_four attack_reference attack_error])
  have random_positive: "0 < momentum_w_state eta mu xs_random N"
    by (rule momentum_positive_margin_transfer[OF eta_nonnegative mu_nonnegative
          mu_less_one effective_at_most_four random_reference random_error])
  have attack_risk:
    "clean_test_risk epsilon (momentum_w_state eta mu xs_attack N) = 1 - epsilon"
    by (rule clean_test_risk_negative[OF attack_negative])
  have random_risk:
    "clean_test_risk epsilon (momentum_w_state eta mu xs_random N) = epsilon"
    by (rule clean_test_risk_positive[OF random_positive])
  have attack_auc:
    "clean_test_auc epsilon (momentum_w_state eta mu xs_attack N) = epsilon"
    by (rule clean_test_auc_negative[OF attack_negative])
  have random_auc:
    "clean_test_auc epsilon (momentum_w_state eta mu xs_random N) = 1 - epsilon"
    by (rule clean_test_auc_positive[OF random_positive])
  show ?thesis using attack_risk random_risk attack_auc random_auc by blast
qed
text \<open>additive_iteration: 加法的摂動を含む反復更新を定める。\<close>

definition additive_iteration ::
    "(real \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "additive_iteration F e x k = perturbed_iteration F 1 e x k"
text \<open>additive_iteration_zero: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma additive_iteration_zero [simp]:
  "additive_iteration F e x 0 = x"
  unfolding additive_iteration_def by simp
text \<open>additive_iteration_Suc: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma additive_iteration_Suc:
  "additive_iteration F e x (Suc k) = F (additive_iteration F e x k) + e k"
  unfolding additive_iteration_def by simp
text \<open>additive_iteration_error_bound: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma additive_iteration_error_bound:
  assumes nonexpansive: "\<And>a b. abs (F a - F b) \<le> abs (a - b)"
  shows "abs (additive_iteration F e x N - (F ^^ N) x) \<le>
    (\<Sum>i<N. abs (e i))"
proof (induction N)
  case 0
  show ?case by simp
next
  case (Suc k)
  let ?actual = "additive_iteration F e x k"
  let ?ideal = "(F ^^ k) x"
  have actual_recurrence:
    "additive_iteration F e x (Suc k) = F ?actual + e k"
    by (rule additive_iteration_Suc)
  have ideal_recurrence: "(F ^^ Suc k) x = F ?ideal"
    by (simp add: funpow_Suc_right)
  have difference_identity:
    "additive_iteration F e x (Suc k) - (F ^^ Suc k) x =
      (F ?actual - F ?ideal) + e k"
    unfolding actual_recurrence ideal_recurrence by algebra
  have triangle:
    "abs (additive_iteration F e x (Suc k) - (F ^^ Suc k) x) \<le>
      abs (F ?actual - F ?ideal) + abs (e k)"
  proof -
    have "abs (additive_iteration F e x (Suc k) - (F ^^ Suc k) x) =
      abs ((F ?actual - F ?ideal) + e k)"
      using difference_identity by simp
    also have "\<dots> \<le> abs (F ?actual - F ?ideal) + abs (e k)"
      by (rule abs_triangle_ineq)
    finally show ?thesis .
  qed
  have dynamics_bound: "abs (F ?actual - F ?ideal) \<le> abs (?actual - ?ideal)"
    by (rule nonexpansive)
  have step_bound:
    "abs (additive_iteration F e x (Suc k) - (F ^^ Suc k) x) \<le>
      abs (?actual - ?ideal) + abs (e k)"
    using triangle dynamics_bound by linarith
  have sum_identity:
    "(\<Sum>i<Suc k. abs (e i)) = (\<Sum>i<k. abs (e i)) + abs (e k)"
    by simp
  show ?case using step_bound Suc.IH sum_identity by linarith
qed
text \<open>additive_perturbation_budget: 加法的摂動と初期ずれの総予算を定める。\<close>

definition additive_perturbation_budget ::
    "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "additive_perturbation_budget e rho N = (\<Sum>i<N. abs (e i)) + abs rho"
text \<open>additive_positive_margin_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma additive_positive_margin_transfer:
  assumes nonexpansive: "\<And>a b. abs (F a - F b) \<le> abs (a - b)"
    and reference_margin: "G \<le> (F ^^ N) x"
    and budget_small: "additive_perturbation_budget e rho N < G"
  shows "0 < additive_iteration F e x N + rho"
proof -
  let ?actual = "additive_iteration F e x N"
  let ?ideal = "(F ^^ N) x"
  let ?sum = "\<Sum>i<N. abs (e i)"
  have comparison: "abs (?actual - ?ideal) \<le> ?sum"
    by (rule additive_iteration_error_bound[OF nonexpansive])
  have reverse_difference: "?ideal - ?actual \<le> ?sum"
    using comparison abs_ge_minus_self[of "?actual - ?ideal"] by linarith
  have residual_lower: "- abs rho \<le> rho"
    using abs_ge_minus_self[of rho] by linarith
  have budget: "?sum + abs rho < G"
    using budget_small unfolding additive_perturbation_budget_def by simp
  show ?thesis using reverse_difference residual_lower reference_margin budget by linarith
qed
text \<open>additive_negative_margin_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma additive_negative_margin_transfer:
  assumes nonexpansive: "\<And>a b. abs (F a - F b) \<le> abs (a - b)"
    and reference_margin: "(F ^^ N) x \<le> -G"
    and budget_small: "additive_perturbation_budget e rho N < G"
  shows "additive_iteration F e x N + rho < 0"
proof -
  let ?actual = "additive_iteration F e x N"
  let ?ideal = "(F ^^ N) x"
  let ?sum = "\<Sum>i<N. abs (e i)"
  have comparison: "abs (?actual - ?ideal) \<le> ?sum"
    by (rule additive_iteration_error_bound[OF nonexpansive])
  have forward_difference: "?actual - ?ideal \<le> ?sum"
    using comparison abs_ge_self[of "?actual - ?ideal"] by linarith
  have residual_upper: "rho \<le> abs rho"
    by (rule abs_ge_self)
  have budget: "?sum + abs rho < G"
    using budget_small unfolding additive_perturbation_budget_def by simp
  show ?thesis using forward_difference residual_upper reference_margin budget by linarith
qed
text \<open>additive_perturbation_inversion_transfer: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem additive_perturbation_inversion_transfer:
  assumes nonexpansive: "\<And>a b. abs (F a - F b) \<le> abs (a - b)"
    and attack_reference: "(F ^^ N) x \<le> -G_attack"
    and random_reference: "G_random \<le> (F ^^ N) y"
    and attack_budget:
      "additive_perturbation_budget e_attack rho_attack N < G_attack"
    and random_budget:
      "additive_perturbation_budget e_random rho_random N < G_random"
  shows "additive_iteration F e_attack x N + rho_attack < 0 \<and>
    0 < additive_iteration F e_random y N + rho_random"
proof -
  have attack_negative:
    "additive_iteration F e_attack x N + rho_attack < 0"
    by (rule additive_negative_margin_transfer[OF nonexpansive attack_reference
          attack_budget])
  have random_positive:
    "0 < additive_iteration F e_random y N + rho_random"
    by (rule additive_positive_margin_transfer[OF nonexpansive random_reference
          random_budget])
  show ?thesis using attack_negative random_positive by blast
qed
text \<open>curriculum_realizable_transfer_error_exact: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma curriculum_realizable_transfer_error_exact:
  "realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k) =
    (1 / real (curriculum_scale k))^4 +
      ((1 / real (curriculum_scale k))^2 -
        (1 / real (curriculum_scale k))^8) / 8"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding realizable_transfer_error_def curriculum_learning_rate_def
      curriculum_realizable_scale_def curriculum_population_def
    using scale_nonzero
    by (simp add: power2_eq_square field_simps; algebra)
qed
text \<open>curriculum_momentum_transfer_error_exact: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma curriculum_momentum_transfer_error_exact:
  "momentum_transfer_error (curriculum_learning_rate k) (1 / 2)
      (curriculum_population k) =
    2 * (1 / real (curriculum_scale k))^4 +
      (1 / real (curriculum_scale k))^2"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding momentum_transfer_error_def momentum_transform_error_def
      momentum_effective_step_def curriculum_learning_rate_def
      curriculum_population_def
    using scale_nonzero
    by (simp add: power2_eq_square field_simps; algebra)
qed
text \<open>curriculum_realizable_transfer_error_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_realizable_transfer_error_tendsto_zero:
  "((\<lambda>k. realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k))
    \<longlongrightarrow> 0) sequentially"
proof -
  let ?r = "\<lambda>k. 1 / real (curriculum_scale k)"
  have ratio_limit: "(?r \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have square_limit: "((\<lambda>k. (?r k)^2) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 2] by simp
  have fourth_limit: "((\<lambda>k. (?r k)^4) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 4] by simp
  have eighth_limit: "((\<lambda>k. (?r k)^8) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 8] by simp
  have difference_limit:
    "((\<lambda>k. (?r k)^2 - (?r k)^8) \<longlongrightarrow> 0) sequentially"
    using tendsto_diff[OF square_limit eighth_limit] by simp
  have scaled_difference_limit:
    "((\<lambda>k. ((?r k)^2 - (?r k)^8) / 8) \<longlongrightarrow> 0) sequentially"
  proof -
    have multiplication_limit:
      "((\<lambda>k. (1 / 8 :: real) * ((?r k)^2 - (?r k)^8)) \<longlongrightarrow>
        (1 / 8) * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const difference_limit])
    show ?thesis using multiplication_limit by simp
  qed
  have total_limit:
    "((\<lambda>k. (?r k)^4 + ((?r k)^2 - (?r k)^8) / 8) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF fourth_limit scaled_difference_limit] by simp
  show ?thesis
    using total_limit
    by (simp add: curriculum_realizable_transfer_error_exact)
qed
text \<open>curriculum_momentum_transfer_error_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_momentum_transfer_error_tendsto_zero:
  "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) (1 / 2)
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?r = "\<lambda>k. 1 / real (curriculum_scale k)"
  have ratio_limit: "(?r \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have square_limit: "((\<lambda>k. (?r k)^2) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 2] by simp
  have fourth_limit: "((\<lambda>k. (?r k)^4) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 4] by simp
  have scaled_fourth_limit: "((\<lambda>k. 2 * (?r k)^4) \<longlongrightarrow> 0) sequentially"
  proof -
    have multiplication_limit:
      "((\<lambda>k. (2::real) * (?r k)^4) \<longlongrightarrow> 2 * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const fourth_limit])
    show ?thesis using multiplication_limit by simp
  qed
  have total_limit: "((\<lambda>k. 2 * (?r k)^4 + (?r k)^2) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF scaled_fourth_limit square_limit] by simp
  show ?thesis
    using total_limit
    by (simp add: curriculum_momentum_transfer_error_exact)
qed
text \<open>curriculum_realizable_transfer_error_eventually_small: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_realizable_transfer_error_eventually_small:
  assumes "0 < G"
  shows "\<forall>\<^sub>F k in sequentially.
    realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k) < G"
proof -
  note eventual_upper = order_tendstoD(2)
    [OF curriculum_realizable_transfer_error_tendsto_zero, of G]
  show ?thesis using eventual_upper assms by simp
qed
text \<open>curriculum_momentum_transfer_error_eventually_small: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_momentum_transfer_error_eventually_small:
  assumes "0 < G"
  shows "\<forall>\<^sub>F k in sequentially.
    momentum_transfer_error (curriculum_learning_rate k) (1 / 2)
      (curriculum_population k) < G"
proof -
  note eventual_upper = order_tendstoD(2)
    [OF curriculum_momentum_transfer_error_tendsto_zero, of G]
  show ?thesis using eventual_upper assms by simp
qed
text \<open>attack_order: アンカーを真、テールを偽に並べる攻撃順序を定める。\<close>

definition attack_order :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "attack_order n m = replicate n True @ replicate m False"
text \<open>binary_logistic_state_true_prefix: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma binary_logistic_state_true_prefix:
  assumes prefix: "\<And>i. i < k \<Longrightarrow> xs ! i = True"
  shows "binary_logistic_state eta q xs k = anchor_state eta k"
using prefix
proof (induction k)
  case 0
  show ?case
    unfolding binary_logistic_state_def anchor_state_def perturbed_iteration_def
    by simp
next
  case (Suc k)
  have current: "xs ! k = True"
    using Suc.prems by simp
  have earlier: "\<And>i. i < k \<Longrightarrow> xs ! i = True"
    using Suc.prems by simp
  have previous: "binary_logistic_state eta q xs k = anchor_state eta k"
    by (rule Suc.IH[OF earlier])
  show ?case
    using current previous
    by (simp add: binary_logistic_state_Suc anchor_state_def
        funpow_Suc_right anchor_step_def bool_value_def sigmoid_neg_identity)
qed
text \<open>binary_logistic_state_false_suffix: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma binary_logistic_state_false_suffix:
  assumes start: "binary_logistic_state eta q xs n = w"
    and suffix: "\<And>j. j < k \<Longrightarrow> xs ! (n + j) = False"
  shows "binary_logistic_state eta q xs (n + k) = ((tail_step eta) ^^ k) w"
using suffix
proof (induction k)
  case 0
  show ?case using start by simp
next
  case (Suc k)
  have current: "xs ! (n + k) = False"
    using Suc.prems by simp
  have earlier: "\<And>j. j < k \<Longrightarrow> xs ! (n + j) = False"
    using Suc.prems by simp
  have previous:
    "binary_logistic_state eta q xs (n + k) = ((tail_step eta) ^^ k) w"
    by (rule Suc.IH[OF earlier])
  have tail_expansion: "tail_step eta = (\<lambda>a. a - eta * sigmoid a)"
    unfolding tail_step_def by (rule ext) simp
  show ?case
    unfolding add_Suc_right tail_step_def
    apply (simp only: binary_logistic_state_Suc previous)
    apply (simp only: tail_expansion)
    using current
    apply (simp add: funpow_Suc_right funpow_swap1 bool_value_def
        tail_step_def)
    done
qed
text \<open>binary_logistic_state_attack_order: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma binary_logistic_state_attack_order:
  "binary_logistic_state eta q (attack_order n m) (n + m) =
    attack_state eta n m"
proof -
  have prefix: "\<And>i. i < n \<Longrightarrow> attack_order n m ! i = True"
  proof -
    fix i
    assume i_less: "i < n"
    show "attack_order n m ! i = True"
      unfolding attack_order_def
      using i_less
      apply (simp only: nth_append length_replicate i_less if_True nth_replicate)
      done
  qed
  have suffix: "\<And>j. j < m \<Longrightarrow> attack_order n m ! (n + j) = False"
  proof -
    fix j
    assume j_less: "j < m"
    have index: "n + j = length (replicate n True) + j"
      by simp
    have offset:
      "(replicate n True @ replicate m False) ! (n + j) =
        replicate m False ! j"
      unfolding index
      by (rule nth_append_length_plus)
    show "attack_order n m ! (n + j) = False"
      unfolding attack_order_def
      using offset j_less
      apply (simp only: nth_replicate)
      done
  qed
  have start:
    "binary_logistic_state eta q (attack_order n m) n = anchor_state eta n"
    by (rule binary_logistic_state_true_prefix[OF prefix])
  show ?thesis
    unfolding attack_state_def
    by (rule binary_logistic_state_false_suffix[OF start suffix])
qed
text \<open>finite_pool_order_only_inversion: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem finite_pool_order_only_inversion:
  fixes eta gamma delta epsilon :: real
  assumes N_positive: "0 < N"
    and counts: "m + n = N"
    and minority_positive: "0 < m"
    and minority_smaller: "m < n"
    and eta_positive: "0 < eta"
    and eta_at_most_four: "eta \<le> 4"
    and gamma_positive: "0 < gamma"
    and delta_positive: "0 < delta"
    and delta_at_most_one: "delta \<le> 1"
    and epsilon_nonnegative: "0 \<le> epsilon"
    and epsilon_below_half: "epsilon < 1 / 2"
    and takeover:
      "ln (1 + real n * (exp eta - 1)) + gamma <
        eta * real m / (1 + exp gamma)"
    and random_margin_positive:
      "0 < random_order_lower_margin eta n m N delta"
  shows "clean_test_risk epsilon (attack_state eta n m) = 1 - epsilon"
    and "clean_test_auc epsilon (attack_state eta n m) = epsilon"
    and "1 - delta \<le> uniform_probability (binary_orders n N)
      {xs. clean_test_risk epsilon
          (binary_logistic_state eta (real n / real N) xs N) = epsilon \<and>
        clean_test_auc epsilon
          (binary_logistic_state eta (real n / real N) xs N) = 1 - epsilon \<and>
        clean_test_risk epsilon
          (binary_logistic_state eta (real n / real N) xs N) <
          clean_test_risk epsilon (attack_state eta n m) \<and>
        clean_test_auc epsilon (attack_state eta n m) <
          clean_test_auc epsilon
            (binary_logistic_state eta (real n / real N) xs N)}"
proof -
  have eta_nonnegative: "0 \<le> eta" using eta_positive by linarith
  have anchor_bound:
    "anchor_state eta n \<le> ln (1 + real n * (exp eta - 1))"
    by (rule anchor_log_bound[OF eta_nonnegative])
  have product_identity:
    "real m * (eta * (1 / (1 + exp gamma))) =
      eta * real m / (1 + exp gamma)"
    unfolding field_class.field_divide_inverse by algebra
  have takeover_form:
    "ln (1 + real n * (exp eta - 1)) -
        real m * (eta * (1 / (1 + exp gamma))) < - gamma"
    using takeover product_identity by linarith
  have attack_negative: "attack_state eta n m < - gamma"
    by (rule logarithmic_anchor_bound_implies_inversion
          [OF eta_positive anchor_bound takeover_form])
  have attack_strictly_negative: "attack_state eta n m < 0"
    using attack_negative gamma_positive by linarith
  have attack_risk:
    "clean_test_risk epsilon (attack_state eta n m) = 1 - epsilon"
    by (rule clean_test_risk_negative[OF attack_strictly_negative])
  have attack_auc:
    "clean_test_auc epsilon (attack_state eta n m) = epsilon"
    by (rule clean_test_auc_negative[OF attack_strictly_negative])
  have random_positive_probability:
    "1 - delta \<le> uniform_probability (binary_orders n N)
      {xs. 0 < binary_logistic_state eta (real n / real N) xs N}"
    by (rule uniform_binary_order_positive_margin[OF N_positive counts
          minority_positive minority_smaller eta_nonnegative eta_at_most_four
          delta_positive delta_at_most_one random_margin_positive])
  let ?positive =
    "{xs. 0 < binary_logistic_state eta (real n / real N) xs N}"
  let ?conclusion =
    "{xs. clean_test_risk epsilon
          (binary_logistic_state eta (real n / real N) xs N) = epsilon \<and>
        clean_test_auc epsilon
          (binary_logistic_state eta (real n / real N) xs N) = 1 - epsilon \<and>
        clean_test_risk epsilon
          (binary_logistic_state eta (real n / real N) xs N) <
          clean_test_risk epsilon (attack_state eta n m) \<and>
        clean_test_auc epsilon (attack_state eta n m) <
          clean_test_auc epsilon
            (binary_logistic_state eta (real n / real N) xs N)}"
  have event_subset: "?positive \<subseteq> ?conclusion"
  proof
    fix xs
    assume "xs \<in> ?positive"
    then have random_positive:
      "0 < binary_logistic_state eta (real n / real N) xs N" by simp
    have random_risk:
      "clean_test_risk epsilon
          (binary_logistic_state eta (real n / real N) xs N) = epsilon"
      by (rule clean_test_risk_positive[OF random_positive])
    have random_auc:
      "clean_test_auc epsilon
          (binary_logistic_state eta (real n / real N) xs N) = 1 - epsilon"
      by (rule clean_test_auc_positive[OF random_positive])
    show "xs \<in> ?conclusion"
      using random_risk random_auc attack_risk attack_auc epsilon_below_half
      by simp
  qed
  have event_probability_mono:
    "uniform_probability (binary_orders n N) ?positive \<le>
      uniform_probability (binary_orders n N) ?conclusion"
    by (rule uniform_probability_mono[OF finite_binary_orders event_subset])
  show "clean_test_risk epsilon (attack_state eta n m) = 1 - epsilon"
    by (rule attack_risk)
  show "clean_test_auc epsilon (attack_state eta n m) = epsilon"
    by (rule attack_auc)
  show "1 - delta \<le> uniform_probability (binary_orders n N) ?conclusion"
    using random_positive_probability event_probability_mono by linarith
qed
text \<open>curriculum_scale_filterlim: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_scale_filterlim:
  "filterlim (\<lambda>k. real (curriculum_scale k)) at_top sequentially"
proof -
  have shifted:
    "filterlim (\<lambda>k. (2::real) + real k) at_top sequentially"
    by (rule filterlim_tendsto_add_at_top[OF tendsto_const
          filterlim_real_sequentially])
  have scaled:
    "filterlim (\<lambda>k. (2::real) * (2 + real k)) at_top sequentially"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ shifted]) simp
  show ?thesis
    unfolding curriculum_scale_def
    using scaled by (simp add: algebra_simps)
qed
text \<open>curriculum_learning_rate_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma curriculum_learning_rate_positive:
  "0 < curriculum_learning_rate k"
  unfolding curriculum_learning_rate_def
  using curriculum_scale_at_least_four[of k] by simp
text \<open>curriculum_learning_rate_at_most_four: 対象量の上界を示す。\<close>

lemma curriculum_learning_rate_at_most_four:
  "curriculum_learning_rate k \<le> 4"
proof -
  have denominator_at_least_one:
    "1 \<le> real (curriculum_scale k) ^ 4"
    using curriculum_scale_at_least_four[of k] by simp
  have "1 / real (curriculum_scale k) ^ 4 \<le> (1::real) / 1"
    by (rule frac_le) (use denominator_at_least_one in simp_all)
  then show ?thesis unfolding curriculum_learning_rate_def by linarith
qed
text \<open>curriculum_population_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma curriculum_population_positive:
  "0 < curriculum_population k"
  unfolding curriculum_population_def
  using curriculum_scale_at_least_four[of k] by simp
text \<open>curriculum_anchor_tail_ratio_exact: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma curriculum_anchor_tail_ratio_exact:
  "real (curriculum_anchor_count k) / real (curriculum_tail_count k) =
    real (curriculum_scale k) - 1"
proof -
  let ?K = "curriculum_scale k"
  have K_positive: "0 < ?K" using curriculum_scale_at_least_four[of k] by simp
  have K_nonzero: "real ?K \<noteq> 0" using K_positive by simp
  have tail_le_population: "?K^5 \<le> ?K^6"
  proof -
    have "?K^5 \<le> ?K^5 * ?K" using K_positive by simp
    also have "\<dots> = ?K^6" by algebra
    finally show ?thesis .
  qed
  have cast_difference:
    "real (?K^6 - ?K^5) = (real ?K)^6 - (real ?K)^5"
    using tail_le_population by simp
  have fifth_power_nonzero: "(real ?K)^5 \<noteq> 0" using K_nonzero by simp
  have quotient_identity:
    "((real ?K)^6 - (real ?K)^5) / (real ?K)^5 = real ?K - 1"
  proof (rule divide_eq_imp[OF fifth_power_nonzero])
    show "(real ?K)^6 - (real ?K)^5 =
      (real ?K - 1) * (real ?K)^5" by algebra
  qed
  show ?thesis
    unfolding curriculum_anchor_count_def curriculum_population_def
      curriculum_tail_count_def
    using cast_difference quotient_identity by simp
qed
text \<open>curriculum_effective_tail_mass: 定義と後続の反転解析で用いる基本性質を示す。\<close>

lemma curriculum_effective_tail_mass:
  "curriculum_learning_rate k * real (curriculum_tail_count k) =
    real (curriculum_scale k)"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding curriculum_learning_rate_def curriculum_tail_count_def
    using scale_nonzero by (simp add: field_simps; algebra)
qed
text \<open>curriculum_log_scale_over_scale_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_log_scale_over_scale_tendsto_zero:
  "((\<lambda>k. ln (real (curriculum_scale k)) / real (curriculum_scale k))
    \<longlongrightarrow> 0) sequentially"
  by (rule filterlim_compose[OF ln_x_over_x_tendsto_0
        curriculum_scale_filterlim])
text \<open>curriculum_anchor_log_upper: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma curriculum_anchor_log_upper:
  "ln (1 + real (curriculum_anchor_count k) *
      (exp (curriculum_learning_rate k) - 1)) \<le>
    1 + 2 * ln (real (curriculum_scale k))"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?eta = "curriculum_learning_rate k"
  have K_positive: "0 < ?K" using curriculum_scale_at_least_four[of k] by simp
  have K_square_at_least_one: "1 \<le> ?K^2"
    using curriculum_scale_at_least_four[of k] by simp
  have eta_positive: "0 < ?eta" by (rule curriculum_learning_rate_positive)
  have eta_at_most_one: "?eta \<le> 1"
  proof -
    have denominator_at_least_one: "1 \<le> ?K^4"
      using curriculum_scale_at_least_four[of k] by simp
    have "1 / ?K^4 \<le> (1::real) / 1"
      by (rule frac_le) (use denominator_at_least_one in simp_all)
    then show ?thesis unfolding curriculum_learning_rate_def by simp
  qed
  have exponential_secant:
    "exp ?eta - 1 \<le> ?eta * (exp 1 - 1)"
  proof -
    have "exp (?eta * 1) \<le> 1 + ?eta * (exp 1 - 1)"
      by (rule exp_secant) (use eta_positive eta_at_most_one in linarith)+
    then show ?thesis by simp
  qed
  have exponential_difference_nonnegative: "0 \<le> exp ?eta - 1"
    using eta_positive by simp
  have anchor_le_population:
    "curriculum_anchor_count k \<le> curriculum_population k"
    using curriculum_counts[of k] by linarith
  have scaled_anchor:
    "real (curriculum_anchor_count k) * (exp ?eta - 1) \<le>
      real (curriculum_population k) * (?eta * (exp 1 - 1))"
  proof -
    have first:
      "real (curriculum_anchor_count k) * (exp ?eta - 1) \<le>
        real (curriculum_population k) * (exp ?eta - 1)"
      by (rule mult_right_mono) (use anchor_le_population
            exponential_difference_nonnegative in simp_all)
    have second:
      "real (curriculum_population k) * (exp ?eta - 1) \<le>
        real (curriculum_population k) * (?eta * (exp 1 - 1))"
      by (rule mult_left_mono[OF exponential_secant]) simp
    show ?thesis using first second by linarith
  qed
  have population_rate: "real (curriculum_population k) * ?eta = ?K^2"
  proof -
    have K_nonzero: "?K \<noteq> 0" using K_positive by simp
    show ?thesis
      unfolding curriculum_population_def curriculum_learning_rate_def
      using K_nonzero by (simp add: field_simps; algebra)
  qed
  have argument_upper:
    "1 + real (curriculum_anchor_count k) * (exp ?eta - 1) \<le>
      exp 1 * ?K^2"
  proof -
    have scaled_identity:
      "real (curriculum_population k) * (?eta * (exp 1 - 1)) =
        ?K^2 * (exp 1 - 1)"
      using population_rate by algebra
    have first:
      "1 + real (curriculum_anchor_count k) * (exp ?eta - 1) \<le>
        1 + ?K^2 * (exp 1 - 1)"
      using scaled_anchor scaled_identity by linarith
    have difference_identity:
      "exp 1 * ?K^2 - (1 + ?K^2 * (exp 1 - 1)) = ?K^2 - 1"
      by algebra
    have second: "1 + ?K^2 * (exp 1 - 1) \<le> exp 1 * ?K^2"
      using K_square_at_least_one difference_identity by linarith
    show ?thesis using first second by linarith
  qed
  have anchor_cast_nonnegative:
    "0 \<le> real (curriculum_anchor_count k)" by simp
  have product_nonnegative:
    "0 \<le> real (curriculum_anchor_count k) * (exp ?eta - 1)"
    by (rule mult_nonneg_nonneg[OF anchor_cast_nonnegative
          exponential_difference_nonnegative])
  have argument_positive:
    "0 < 1 + real (curriculum_anchor_count k) * (exp ?eta - 1)"
    using product_nonnegative by linarith
  have logarithm_upper:
    "ln (1 + real (curriculum_anchor_count k) * (exp ?eta - 1)) \<le>
      ln (exp 1 * ?K^2)"
    by (rule ln_mono[OF argument_upper argument_positive])
  have logarithm_identity: "ln (exp 1 * ?K^2) = 1 + 2 * ln ?K"
    using K_positive by (simp add: ln_mult ln_realpow)
  show ?thesis using logarithm_upper logarithm_identity by simp
qed
text \<open>curriculum_anchor_log_over_scale_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_anchor_log_over_scale_tendsto_zero:
  "((\<lambda>k. ln (1 + real (curriculum_anchor_count k) *
      (exp (curriculum_learning_rate k) - 1)) /
      real (curriculum_scale k)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?A = "\<lambda>k. ln (1 + real (curriculum_anchor_count k) *
    (exp (curriculum_learning_rate k) - 1))"
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. inverse (?K k)) \<longlongrightarrow> 0) sequentially"
      by (rule tendsto_inverse_0_at_top[OF curriculum_scale_filterlim])
    then show ?thesis by (simp add: field_class.field_divide_inverse)
  qed
  have twice_log_limit:
    "((\<lambda>k. 2 * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (2::real) * (ln (?K k) / ?K k))
        \<longlongrightarrow> 2 * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const
            curriculum_log_scale_over_scale_tendsto_zero])
    then show ?thesis by simp
  qed
  have upper_limit:
    "((\<lambda>k. (1 + 2 * ln (?K k)) / ?K k)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have sum_limit:
      "((\<lambda>k. 1 / ?K k + 2 * (ln (?K k) / ?K k))
        \<longlongrightarrow> 0) sequentially"
      using tendsto_add[OF inverse_limit twice_log_limit] by simp
    have identity:
      "(1 + 2 * ln (?K k)) / ?K k =
        1 / ?K k + 2 * (ln (?K k) / ?K k)" for k
      unfolding field_class.field_divide_inverse by algebra
    show ?thesis using sum_limit by (simp add: identity)
  qed
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 0 \<le> ?A k / ?K k"
  proof (intro always_eventually allI)
    fix k
    have exponential_difference_nonnegative:
      "0 \<le> exp (curriculum_learning_rate k) - 1"
      using curriculum_learning_rate_positive[of k] by simp
    have product_nonnegative:
      "0 \<le> real (curriculum_anchor_count k) *
        (exp (curriculum_learning_rate k) - 1)"
      by (rule mult_nonneg_nonneg) (use exponential_difference_nonnegative in simp_all)
    have logarithm_nonnegative: "0 \<le> ?A k"
      using product_nonnegative by simp
    have scale_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    show "0 \<le> ?A k / ?K k"
      by (rule divide_nonneg_nonneg) (use logarithm_nonnegative scale_positive in linarith)+
  qed
  have upper_bound:
    "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k \<le> (1 + 2 * ln (?K k)) / ?K k"
  proof (intro always_eventually allI)
    fix k
    have scale_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    show "?A k / ?K k \<le> (1 + 2 * ln (?K k)) / ?K k"
      by (rule divide_right_mono[OF curriculum_anchor_log_upper])
        (use scale_positive in linarith)
  qed
  show ?thesis
    by (rule tendsto_sandwich[OF lower_bound upper_bound tendsto_const upper_limit])
qed
text \<open>curriculum_tail_takeover_eventually: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_tail_takeover_eventually:
  "\<forall>\<^sub>F k in sequentially.
    ln (1 + real (curriculum_anchor_count k) *
      (exp (curriculum_learning_rate k) - 1)) + 1 <
    curriculum_learning_rate k * real (curriculum_tail_count k) /
      (1 + exp 1)"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?A = "\<lambda>k. ln (1 + real (curriculum_anchor_count k) *
    (exp (curriculum_learning_rate k) - 1))"
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. inverse (?K k)) \<longlongrightarrow> 0) sequentially"
      by (rule tendsto_inverse_0_at_top[OF curriculum_scale_filterlim])
    then show ?thesis by (simp add: field_class.field_divide_inverse)
  qed
  have normalized_limit:
    "((\<lambda>k. ?A k / ?K k + 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF curriculum_anchor_log_over_scale_tendsto_zero
          inverse_limit] by simp
  have denominator_positive: "0 < 1 + exp (1::real)"
    using exp_gt_zero[of "1::real"] by linarith
  have target_positive: "0 < (1::real) / (1 + exp 1)"
    by (rule divide_pos_pos) (use denominator_positive in simp_all)
  have eventual_normalized:
    "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k + 1 / ?K k < 1 / (1 + exp 1)"
    using order_tendstoD(2)[OF normalized_limit, of "1 / (1 + exp 1)"]
      target_positive by simp
  show ?thesis
  proof (rule eventually_mono[OF eventual_normalized])
    fix k
    assume normalized:
      "?A k / ?K k + 1 / ?K k < 1 / (1 + exp 1)"
    have scale_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have normalized_identity:
      "?A k / ?K k + 1 / ?K k = (?A k + 1) / ?K k"
      unfolding field_class.field_divide_inverse by algebra
    have unnormalized:
      "?A k + 1 < (1 / (1 + exp 1)) * ?K k"
      using normalized normalized_identity scale_positive
      by (simp add: pos_divide_less_eq)
    have target_identity:
      "(1 / (1 + exp 1)) * ?K k =
        curriculum_learning_rate k * real (curriculum_tail_count k) /
          (1 + exp 1)"
      using curriculum_effective_tail_mass[of k]
      by (simp add: field_class.field_divide_inverse mult.commute)
    show "?A k + 1 <
      curriculum_learning_rate k * real (curriculum_tail_count k) /
        (1 + exp 1)"
      using unnormalized target_identity by linarith
  qed
qed
text \<open>curriculum_attack_margin_eventually: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_attack_margin_eventually:
  "\<forall>\<^sub>F k in sequentially.
    attack_state (curriculum_learning_rate k)
      (curriculum_anchor_count k) (curriculum_tail_count k) < -1"
proof -
  show ?thesis
  proof (rule eventually_mono[OF curriculum_tail_takeover_eventually])
    fix k
    assume takeover:
      "ln (1 + real (curriculum_anchor_count k) *
        (exp (curriculum_learning_rate k) - 1)) + 1 <
       curriculum_learning_rate k * real (curriculum_tail_count k) /
        (1 + exp 1)"
    have eta_positive: "0 < curriculum_learning_rate k"
      by (rule curriculum_learning_rate_positive)
    have eta_nonnegative: "0 \<le> curriculum_learning_rate k"
      using eta_positive by linarith
    have anchor_bound:
      "anchor_state (curriculum_learning_rate k) (curriculum_anchor_count k) \<le>
        ln (1 + real (curriculum_anchor_count k) *
          (exp (curriculum_learning_rate k) - 1))"
      by (rule anchor_log_bound[OF eta_nonnegative])
    have product_identity:
      "real (curriculum_tail_count k) *
          (curriculum_learning_rate k * (1 / (1 + exp 1))) =
        curriculum_learning_rate k * real (curriculum_tail_count k) /
          (1 + exp 1)"
      unfolding field_class.field_divide_inverse by algebra
    have takeover_form:
      "ln (1 + real (curriculum_anchor_count k) *
          (exp (curriculum_learning_rate k) - 1)) -
        real (curriculum_tail_count k) *
          (curriculum_learning_rate k * (1 / (1 + exp 1))) < -1"
      using takeover product_identity by linarith
    show "attack_state (curriculum_learning_rate k)
        (curriculum_anchor_count k) (curriculum_tail_count k) < -1"
      by (rule logarithmic_anchor_bound_implies_inversion
            [OF eta_positive anchor_bound takeover_form])
  qed
qed
text \<open>curriculum_tail_fraction_exact: 対象量の厳密な閉形式を示す。\<close>

lemma curriculum_tail_fraction_exact:
  "real (curriculum_tail_count k) / real (curriculum_population k) =
    1 / real (curriculum_scale k)"
  using curriculum_tail_ratio_exact[of k]
  unfolding curriculum_tail_ratio_def .
text \<open>curriculum_anchor_fraction_exact: 対象量の厳密な閉形式を示す。\<close>

lemma curriculum_anchor_fraction_exact:
  "real (curriculum_anchor_count k) / real (curriculum_population k) =
    1 - 1 / real (curriculum_scale k)"
proof -
  have cast_counts:
    "real (curriculum_tail_count k) + real (curriculum_anchor_count k) =
      real (curriculum_population k)"
    using arg_cong[OF curriculum_counts[of k], of "\<lambda>n. real n"] by simp
  have population_nonzero: "real (curriculum_population k) \<noteq> 0"
    using curriculum_population_positive[of k] by simp
  have fraction_sum:
    "real (curriculum_tail_count k) / real (curriculum_population k) +
      real (curriculum_anchor_count k) / real (curriculum_population k) = 1"
    using cast_counts population_nonzero
    by (simp add: add_divide_distrib[symmetric])
  show ?thesis using fraction_sum curriculum_tail_fraction_exact[of k] by linarith
qed
text \<open>curriculum_log_odds_exact: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma curriculum_log_odds_exact:
  "ln ((real (curriculum_anchor_count k) / real (curriculum_population k)) /
      (real (curriculum_tail_count k) / real (curriculum_population k))) =
    ln (real (curriculum_scale k) - 1)"
proof -
  have tail_fraction_positive:
    "0 < real (curriculum_tail_count k) / real (curriculum_population k)"
    using curriculum_tail_positive[of k] curriculum_population_positive[of k]
    by (intro divide_pos_pos) simp_all
  have ratio_identity:
    "(real (curriculum_anchor_count k) / real (curriculum_population k)) /
      (real (curriculum_tail_count k) / real (curriculum_population k)) =
      real (curriculum_anchor_count k) / real (curriculum_tail_count k)"
    using tail_fraction_positive curriculum_population_positive[of k]
    by (simp add: field_simps)
  show ?thesis
    using ratio_identity curriculum_anchor_tail_ratio_exact[of k] by simp
qed
text \<open>curriculum_population_learning_mass: カリキュラムの個数または母集団分解を整理する。\<close>

lemma curriculum_population_learning_mass:
  "real (curriculum_population k) * curriculum_learning_rate k =
    real (curriculum_scale k)^2"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding curriculum_population_def curriculum_learning_rate_def
    using scale_nonzero by (simp add: field_simps; algebra)
qed
text \<open>curriculum_contraction_mass_exact: 更新写像の収縮係数とその漸近評価を示す。\<close>

lemma curriculum_contraction_mass_exact:
  "real (curriculum_population k) * curriculum_learning_rate k *
      (real (curriculum_tail_count k) / real (curriculum_population k)) *
      (real (curriculum_anchor_count k) / real (curriculum_population k)) =
    real (curriculum_scale k) - 1"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_nonzero: "?K \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have algebraic_identity:
    "?K^2 * (1 / ?K) * (1 - 1 / ?K) = ?K - 1"
    using K_nonzero by (simp add: field_simps; algebra)
  show ?thesis
    using curriculum_population_learning_mass[of k]
      curriculum_tail_fraction_exact[of k]
      curriculum_anchor_fraction_exact[of k] algebraic_identity
    by simp
qed
text \<open>curriculum_contraction_power_le_exp: 更新写像の収縮係数とその漸近評価を示す。\<close>

lemma curriculum_contraction_power_le_exp:
  "(1 - curriculum_learning_rate k *
      (real (curriculum_tail_count k) / real (curriculum_population k)) *
      (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
      curriculum_population k \<le>
    exp (-(real (curriculum_scale k) - 1))"
proof -
  let ?eta = "curriculum_learning_rate k"
  let ?p = "real (curriculum_tail_count k) / real (curriculum_population k)"
  let ?q = "real (curriculum_anchor_count k) / real (curriculum_population k)"
  let ?x = "?eta * ?p * ?q"
  let ?N = "curriculum_population k"
  have eta_nonnegative: "0 \<le> ?eta"
    using curriculum_learning_rate_positive[of k] by linarith
  have eta_at_most_one: "?eta \<le> 1"
  proof -
    have denominator_at_least_one:
      "1 \<le> real (curriculum_scale k)^4"
      using curriculum_scale_at_least_four[of k] by simp
    have "1 / real (curriculum_scale k)^4 \<le> (1::real) / 1"
      by (rule frac_le) (use denominator_at_least_one in simp_all)
    then show ?thesis unfolding curriculum_learning_rate_def by simp
  qed
  have p_nonnegative: "0 \<le> ?p"
    using curriculum_tail_positive[of k] curriculum_population_positive[of k]
    by (intro divide_nonneg_nonneg) simp_all
  have p_at_most_one: "?p \<le> 1"
  proof -
    have count_le: "curriculum_tail_count k \<le> curriculum_population k"
      using curriculum_counts[of k] by linarith
    have cast_le:
      "real (curriculum_tail_count k) \<le> real (curriculum_population k)"
      using count_le by simp
    have population_real_positive: "0 < real (curriculum_population k)"
      using curriculum_population_positive[of k] by simp
    show ?thesis using cast_le
      by (simp only: divide_le_eq_1_pos[OF population_real_positive])
  qed
  have q_nonnegative: "0 \<le> ?q"
    using curriculum_population_positive[of k]
    by (intro divide_nonneg_nonneg) simp_all
  have q_at_most_one: "?q \<le> 1"
  proof -
    have count_le: "curriculum_anchor_count k \<le> curriculum_population k"
      using curriculum_counts[of k] by linarith
    have cast_le:
      "real (curriculum_anchor_count k) \<le> real (curriculum_population k)"
      using count_le by simp
    have population_real_positive: "0 < real (curriculum_population k)"
      using curriculum_population_positive[of k] by simp
    show ?thesis using cast_le
      by (simp only: divide_le_eq_1_pos[OF population_real_positive])
  qed
  have eta_p_nonnegative: "0 \<le> ?eta * ?p"
    by (rule mult_nonneg_nonneg[OF eta_nonnegative p_nonnegative])
  have eta_p_at_most_one: "?eta * ?p \<le> 1"
  proof -
    have "?eta * ?p \<le> 1 * ?p"
      by (rule mult_right_mono[OF eta_at_most_one p_nonnegative])
    also have "\<dots> \<le> 1" using p_at_most_one by simp
    finally show ?thesis .
  qed
  have x_nonnegative: "0 \<le> ?x"
    by (rule mult_nonneg_nonneg[OF eta_p_nonnegative q_nonnegative])
  have x_at_most_one: "?x \<le> 1"
  proof -
    have "?eta * ?p * ?q \<le> 1 * ?q"
      by (rule mult_right_mono[OF eta_p_at_most_one q_nonnegative])
    also have "\<dots> \<le> 1" using q_at_most_one by simp
    finally show ?thesis .
  qed
  have one_minus_nonnegative: "0 \<le> 1 - ?x" using x_at_most_one by linarith
  have step_bound: "1 - ?x \<le> exp (-?x)" by (rule exp_minus_ge)
  have power_bound: "(1 - ?x)^?N \<le> (exp (-?x))^?N"
    by (rule power_mono[OF step_bound one_minus_nonnegative])
  have mass_identity: "real ?N * ?x = real (curriculum_scale k) - 1"
    using curriculum_contraction_mass_exact[of k] by algebra
  have exponential_identity:
    "(exp (-?x))^?N = exp (-(real (curriculum_scale k) - 1))"
  proof -
    have "(exp (-?x))^?N = exp (real ?N * (-?x))"
      by (rule exp_of_nat_mult[symmetric])
    also have "\<dots> = exp (-(real ?N * ?x))"
    proof -
      have exponent_identity: "real ?N * (-?x) = -(real ?N * ?x)"
        by algebra
      show ?thesis using exponent_identity by simp
    qed
    also have "\<dots> = exp (-(real (curriculum_scale k) - 1))"
      using mass_identity by simp
    finally show ?thesis .
  qed
  show ?thesis using power_bound exponential_identity by simp
qed
text \<open>curriculum_exp_contraction_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_exp_contraction_tendsto_zero:
  "((\<lambda>k. exp (-(real (curriculum_scale k) - 1)))
    \<longlongrightarrow> 0) sequentially"
proof -
  have shifted:
    "filterlim (\<lambda>k. real (curriculum_scale k) - 1) at_top sequentially"
  proof -
    have "filterlim (\<lambda>k. (-1::real) + real (curriculum_scale k))
        at_top sequentially"
      by (rule filterlim_tendsto_add_at_top[OF tendsto_const
            curriculum_scale_filterlim])
    then show ?thesis by simp
  qed
  have negative:
    "filterlim (\<lambda>k. -(real (curriculum_scale k) - 1))
      at_bot sequentially"
    using shifted by (simp add: filterlim_uminus_at_bot)
  show ?thesis by (rule filterlim_compose[OF exp_at_bot negative])
qed
text \<open>curriculum_contraction_factor_eventually_half: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_contraction_factor_eventually_half:
  "\<forall>\<^sub>F k in sequentially.
    1 / 2 \<le> 1 -
      (1 - curriculum_learning_rate k *
        (real (curriculum_tail_count k) / real (curriculum_population k)) *
        (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
        curriculum_population k"
proof -
  have exp_small:
    "\<forall>\<^sub>F k in sequentially.
      exp (-(real (curriculum_scale k) - 1)) < 1 / 2"
    using order_tendstoD(2)[OF curriculum_exp_contraction_tendsto_zero,
        of "1 / 2"]
    by simp
  show ?thesis
  proof (rule eventually_mono[OF exp_small])
    fix k
    assume upper: "exp (-(real (curriculum_scale k) - 1)) < 1 / 2"
    have power_upper:
      "(1 - curriculum_learning_rate k *
        (real (curriculum_tail_count k) / real (curriculum_population k)) *
        (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
        curriculum_population k < 1 / 2"
      using curriculum_contraction_power_le_exp[of k] upper by linarith
    show "1 / 2 \<le> 1 -
      (1 - curriculum_learning_rate k *
        (real (curriculum_tail_count k) / real (curriculum_population k)) *
        (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
        curriculum_population k"
      using power_upper by linarith
  qed
qed
text \<open>curriculum_confidence_exact: 対象量の厳密な閉形式を示す。\<close>

lemma curriculum_confidence_exact:
  "curriculum_confidence k = curriculum_tail_ratio k ^ 12"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding curriculum_confidence_def curriculum_tail_ratio_def
      curriculum_tail_count_def curriculum_population_def
    using scale_nonzero by (simp add: field_simps; algebra)
qed
text \<open>curriculum_confidence_positive: 対象量が正であること、または正側の評価を示す。\<close>

lemma curriculum_confidence_positive:
  "0 < curriculum_confidence k"
  unfolding curriculum_confidence_def
  using curriculum_scale_at_least_four[of k]
  by (intro divide_pos_pos) simp_all
text \<open>curriculum_confidence_at_most_one: 対象量の上界を示す。\<close>

lemma curriculum_confidence_at_most_one:
  "curriculum_confidence k \<le> 1"
proof -
  have denominator_at_least_one:
    "1 \<le> real (curriculum_scale k)^12"
    using curriculum_scale_at_least_four[of k] by simp
  have "1 / real (curriculum_scale k)^12 \<le> (1::real) / 1"
    by (rule frac_le) (use denominator_at_least_one in simp_all)
  then show ?thesis unfolding curriculum_confidence_def by simp
qed
text \<open>curriculum_confidence_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_confidence_tendsto_zero:
  "(curriculum_confidence \<longlongrightarrow> 0) sequentially"
proof -
  have "((\<lambda>k. curriculum_tail_ratio k ^ 12)
      \<longlongrightarrow> 0 ^ 12) sequentially"
    by (rule tendsto_power[OF curriculum_tail_ratio_tendsto_zero])
  note power_limit = this
  have function_identity:
    "curriculum_confidence = (\<lambda>k. curriculum_tail_ratio k ^ 12)"
    by (rule ext) (simp add: curriculum_confidence_exact)
  show ?thesis using power_limit function_identity by simp
qed
text \<open>curriculum_random_error: カリキュラムのランダム順序誤差を定める。\<close>

definition curriculum_random_error :: "nat \<Rightarrow> real" where
  "curriculum_random_error k =
    curriculum_learning_rate k *
      sqrt (real (curriculum_population k) / 2 *
        ln (2 * real (curriculum_population k) / curriculum_confidence k))"
text \<open>curriculum_random_log_argument: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma curriculum_random_log_argument:
  "2 * real (curriculum_population k) / curriculum_confidence k =
    2 * real (curriculum_scale k)^18"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    unfolding curriculum_population_def curriculum_confidence_def
    using scale_nonzero by (simp add: field_simps; algebra)
qed
text \<open>curriculum_random_log_nonnegative: 対数またはロジット比をスケール量に結び付ける。\<close>

lemma curriculum_random_log_nonnegative:
  "0 \<le> ln (2 * real (curriculum_population k) / curriculum_confidence k)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_at_least_one: "1 \<le> ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have K_power_at_least_one: "1 \<le> ?K^18"
    by (rule one_le_power[OF K_at_least_one])
  have argument_at_least_one: "1 \<le> 2 * ?K^18"
    using K_power_at_least_one by linarith
  have "0 \<le> ln (2 * ?K^18)" using argument_at_least_one by simp
  then show ?thesis using curriculum_random_log_argument[of k] by simp
qed
text \<open>curriculum_random_error_nonnegative: 誤差または状態の明示的な上界を与える。\<close>

lemma curriculum_random_error_nonnegative:
  "0 \<le> curriculum_random_error k"
proof -
  have eta_nonnegative: "0 \<le> curriculum_learning_rate k"
    using curriculum_learning_rate_positive[of k] by linarith
  have population_factor_nonnegative:
    "0 \<le> real (curriculum_population k) / 2" by simp
  have inside_nonnegative:
    "0 \<le> real (curriculum_population k) / 2 *
      ln (2 * real (curriculum_population k) / curriculum_confidence k)"
    by (rule mult_nonneg_nonneg[OF population_factor_nonnegative
          curriculum_random_log_nonnegative])
  have root_nonnegative:
    "0 \<le> sqrt (real (curriculum_population k) / 2 *
      ln (2 * real (curriculum_population k) / curriculum_confidence k))"
    by (rule real_sqrt_ge_zero[OF inside_nonnegative])
  show ?thesis unfolding curriculum_random_error_def
    by (rule mult_nonneg_nonneg[OF eta_nonnegative root_nonnegative])
qed
text \<open>curriculum_random_error_square: 誤差または状態の明示的な上界を与える。\<close>

lemma curriculum_random_error_square:
  "curriculum_random_error k ^ 2 =
    ln (2 * real (curriculum_scale k)^18) /
      (2 * real (curriculum_scale k)^2)"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?L = "ln (2 * real (curriculum_population k) / curriculum_confidence k)"
  let ?X = "real (curriculum_population k) / 2 * ?L"
  have K_positive: "0 < ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have logarithm_nonnegative: "0 \<le> ?L"
    by (rule curriculum_random_log_nonnegative)
  have X_nonnegative: "0 \<le> ?X"
    by (rule mult_nonneg_nonneg) (use logarithm_nonnegative in simp_all)
  have square_expansion:
    "curriculum_random_error k ^ 2 =
      curriculum_learning_rate k ^ 2 * ?X"
    unfolding curriculum_random_error_def
    using X_nonnegative by (simp add: power_mult_distrib)
  have coefficient_identity:
    "curriculum_learning_rate k ^ 2 *
      (real (curriculum_population k) / 2) = 1 / (2 * ?K^2)"
    unfolding curriculum_learning_rate_def curriculum_population_def
    using K_positive by (simp add: field_simps; algebra)
  show ?thesis
    using square_expansion coefficient_identity curriculum_random_log_argument[of k]
    by algebra
qed
text \<open>curriculum_random_error_square_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_random_error_square_tendsto_zero:
  "((\<lambda>k. curriculum_random_error k ^ 2)
    \<longlongrightarrow> 0) sequentially"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. inverse (?K k)) \<longlongrightarrow> 0) sequentially"
      by (rule tendsto_inverse_0_at_top[OF curriculum_scale_filterlim])
    then show ?thesis by (simp add: field_class.field_divide_inverse)
  qed
  have inverse_square_limit:
    "((\<lambda>k. (1 / ?K k)^2) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (1 / ?K k)^2) \<longlongrightarrow> 0^2) sequentially"
      by (rule tendsto_power[OF inverse_limit])
    then show ?thesis by simp
  qed
  have constant_term_limit:
    "((\<lambda>k. (ln 2 / 2) * (1 / ?K k)^2)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (ln 2 / 2) * (1 / ?K k)^2)
        \<longlongrightarrow> (ln 2 / 2) * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const inverse_square_limit])
    then show ?thesis by simp
  qed
  have logarithmic_product_limit:
    "((\<lambda>k. (ln (?K k) / ?K k) * (1 / ?K k))
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF curriculum_log_scale_over_scale_tendsto_zero
          inverse_limit]
    by simp
  have logarithmic_term_limit:
    "((\<lambda>k. 9 * ((ln (?K k) / ?K k) * (1 / ?K k)))
      \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (9::real) *
        ((ln (?K k) / ?K k) * (1 / ?K k)))
        \<longlongrightarrow> 9 * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const logarithmic_product_limit])
    then show ?thesis by simp
  qed
  have sum_limit:
    "((\<lambda>k. (ln 2 / 2) * (1 / ?K k)^2 +
        9 * ((ln (?K k) / ?K k) * (1 / ?K k)))
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF constant_term_limit logarithmic_term_limit] by simp
  have identity:
    "ln (2 * ?K k^18) / (2 * ?K k^2) =
      (ln 2 / 2) * (1 / ?K k)^2 +
        9 * ((ln (?K k) / ?K k) * (1 / ?K k))" for k
  proof -
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have logarithm_identity: "ln (2 * ?K k^18) = ln 2 + 18 * ln (?K k)"
      using K_positive by (simp add: ln_mult ln_realpow)
    have inverse_product:
      "inverse (2 * ?K k^2) = inverse 2 * inverse (?K k) * inverse (?K k)"
      by (simp add: power2_eq_square)
    show ?thesis
      unfolding field_class.field_divide_inverse
      using logarithm_identity inverse_product by algebra
  qed
  have normalized_limit:
    "((\<lambda>k. ln (2 * ?K k^18) / (2 * ?K k^2))
      \<longlongrightarrow> 0) sequentially"
    using sum_limit by (simp add: identity)
  show ?thesis
    using normalized_limit by (simp add: curriculum_random_error_square)
qed
text \<open>curriculum_random_error_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_random_error_tendsto_zero:
  "(curriculum_random_error \<longlongrightarrow> 0) sequentially"
proof -
  have square_limit:
    "((\<lambda>k. curriculum_random_error k ^ 2)
      \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_random_error_square_tendsto_zero)
  have root_limit:
    "((\<lambda>k. sqrt (curriculum_random_error k ^ 2))
      \<longlongrightarrow> sqrt 0) sequentially"
    by (rule tendsto_real_sqrt[OF square_limit])
  have function_identity:
    "(\<lambda>k. sqrt (curriculum_random_error k ^ 2)) = curriculum_random_error"
  proof (rule ext)
    fix k
    show "sqrt (curriculum_random_error k ^ 2) = curriculum_random_error k"
      using curriculum_random_error_nonnegative[of k]
      by simp
  qed
  show ?thesis using root_limit function_identity by simp
qed
text \<open>curriculum_log_odds_filterlim: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_log_odds_filterlim:
  "filterlim (\<lambda>k. ln (real (curriculum_scale k) - 1))
    at_top sequentially"
proof -
  have shifted:
    "filterlim (\<lambda>k. real (curriculum_scale k) - 1) at_top sequentially"
  proof -
    have "filterlim (\<lambda>k. (-1::real) + real (curriculum_scale k))
        at_top sequentially"
      by (rule filterlim_tendsto_add_at_top[OF tendsto_const
            curriculum_scale_filterlim])
    then show ?thesis by simp
  qed
  have logarithm_filterlim:
    "filterlim (\<lambda>k. ln (real (curriculum_scale k) - 1))
      at_top sequentially"
    by (rule filterlim_compose[OF ln_at_top shifted])
  show ?thesis using logarithm_filterlim
    by (simp add: curriculum_log_odds_exact)
qed
text \<open>curriculum_random_margin_exact: 更新後の分類マージンを評価する。\<close>

lemma curriculum_random_margin_exact:
  "random_order_lower_margin
      (curriculum_learning_rate k) (curriculum_anchor_count k)
      (curriculum_tail_count k) (curriculum_population k)
      (curriculum_confidence k) =
    ln (real (curriculum_scale k) - 1) *
      (1 - (1 - curriculum_learning_rate k *
        (real (curriculum_tail_count k) / real (curriculum_population k)) *
        (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
        curriculum_population k) - curriculum_random_error k"
  unfolding random_order_lower_margin_def curriculum_random_error_def
  using curriculum_log_odds_exact[of k]
  by simp
text \<open>curriculum_random_margin_eventually_gt_one: 更新後の分類マージンを評価する。\<close>

lemma curriculum_random_margin_eventually_gt_one:
  "\<forall>\<^sub>F k in sequentially.
    1 < random_order_lower_margin
      (curriculum_learning_rate k) (curriculum_anchor_count k)
      (curriculum_tail_count k) (curriculum_population k)
      (curriculum_confidence k)"
proof -
  have logarithm_large:
    "\<forall>\<^sub>F k in sequentially.
      4 \<le> ln (real (curriculum_scale k) - 1)"
    using curriculum_log_odds_filterlim
    unfolding filterlim_at_top by simp
  have error_small:
    "\<forall>\<^sub>F k in sequentially. curriculum_random_error k < 1"
    using order_tendstoD(2)[OF curriculum_random_error_tendsto_zero, of "1"]
    by simp
  note combined = eventually_conj[OF logarithm_large
      eventually_conj[OF curriculum_contraction_factor_eventually_half error_small]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume facts:
      "4 \<le> ln (real (curriculum_scale k) - 1) \<and>
       1 / 2 \<le> 1 -
        (1 - curriculum_learning_rate k *
          (real (curriculum_tail_count k) / real (curriculum_population k)) *
          (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
          curriculum_population k \<and>
       curriculum_random_error k < 1"
    let ?L = "ln (real (curriculum_scale k) - 1)"
    let ?C = "1 -
      (1 - curriculum_learning_rate k *
        (real (curriculum_tail_count k) / real (curriculum_population k)) *
        (real (curriculum_anchor_count k) / real (curriculum_population k))) ^
        curriculum_population k"
    have L_nonnegative: "0 \<le> ?L" using facts by linarith
    have C_nonnegative: "0 \<le> ?C" using facts by linarith
    have product_lower: "4 * (1 / 2) \<le> ?L * ?C"
      by (rule mult_mono) (use facts L_nonnegative C_nonnegative in linarith)+
    show "1 < random_order_lower_margin
      (curriculum_learning_rate k) (curriculum_anchor_count k)
      (curriculum_tail_count k) (curriculum_population k)
      (curriculum_confidence k)"
      using product_lower facts curriculum_random_margin_exact[of k] by linarith
  qed
qed
text \<open>curriculum_momentum_transfer_error_exact_general: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma curriculum_momentum_transfer_error_exact_general:
  assumes mu_less_one: "mu < 1"
  shows "momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k) =
    (mu / (1 - mu)^2) * (1 / real (curriculum_scale k))^4 +
    (mu / (4 * (1 - mu)^3)) * (1 / real (curriculum_scale k))^2"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?r = "1 / ?K"
  let ?d = "1 - mu"
  have scale_nonzero: "?K \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have rate_inverse_identity:
    "curriculum_learning_rate k = (inverse ?K)^4"
    unfolding curriculum_learning_rate_def field_class.field_divide_inverse
    by (simp add: power_inverse)
  have inverse_square: "inverse (?d^2) = inverse ?d * inverse ?d"
    by (simp add: power2_eq_square)
  have transform_identity:
    "momentum_transform_error (curriculum_learning_rate k) mu =
      mu * inverse ?d * inverse ?d * (inverse ?K)^4"
    unfolding momentum_transform_error_def field_class.field_divide_inverse
    using rate_inverse_identity inverse_square by algebra
  have effective_mass_identity:
    "real (curriculum_population k) *
      momentum_effective_step (curriculum_learning_rate k) mu =
      ?K^2 * inverse ?d"
    unfolding momentum_effective_step_def field_class.field_divide_inverse
    using curriculum_population_learning_mass[of k] by algebra
  have scale_inverse_identity: "?K * inverse ?K = 1"
    using scale_nonzero by simp
  have scale_product_identity:
    "?K^2 * (inverse ?K)^4 = (inverse ?K)^2"
    using scale_inverse_identity by algebra
  have inverse_coefficient:
    "inverse (4 * ?d^3) = inverse 4 * inverse ?d * inverse ?d * inverse ?d"
    by (simp add: power3_eq_cube)
  have "momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k) =
    momentum_transform_error (curriculum_learning_rate k) mu *
      (1 + real (curriculum_population k) *
        momentum_effective_step (curriculum_learning_rate k) mu / 4)"
    by (rule momentum_transfer_error_def)
  also have "\<dots> =
    (mu * inverse ?d * inverse ?d * (inverse ?K)^4) *
      (1 + (?K^2 * inverse ?d) / 4)"
    using transform_identity effective_mass_identity by simp
  also have "\<dots> =
    mu * inverse ?d * inverse ?d * (inverse ?K)^4 +
    mu * inverse 4 * inverse ?d * inverse ?d * inverse ?d *
      (?K^2 * (inverse ?K)^4)"
    by algebra
  also have "\<dots> =
    mu * inverse ?d * inverse ?d * (inverse ?K)^4 +
    mu * inverse 4 * inverse ?d * inverse ?d * inverse ?d *
      (inverse ?K)^2"
    using scale_product_identity by simp
  also have "\<dots> =
    (mu / ?d^2) * ?r^4 +
    (mu / (4 * ?d^3)) * ?r^2"
    unfolding field_class.field_divide_inverse
    using inverse_square inverse_coefficient by algebra
  finally show ?thesis .
qed
text \<open>curriculum_momentum_transfer_error_tendsto_zero_general: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma curriculum_momentum_transfer_error_tendsto_zero_general:
  assumes mu_less_one: "mu < 1"
  shows "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?r = "\<lambda>k. 1 / real (curriculum_scale k)"
  have ratio_limit: "(?r \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have square_limit: "((\<lambda>k. (?r k)^2) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 2] by simp
  have fourth_limit: "((\<lambda>k. (?r k)^4) \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF ratio_limit, of 4] by simp
  have first_term_limit:
    "((\<lambda>k. (mu / (1 - mu)^2) * (?r k)^4)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (mu / (1 - mu)^2) * (?r k)^4)
        \<longlongrightarrow> (mu / (1 - mu)^2) * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const fourth_limit])
    then show ?thesis by simp
  qed
  have second_term_limit:
    "((\<lambda>k. (mu / (4 * (1 - mu)^3)) * (?r k)^2)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>k. (mu / (4 * (1 - mu)^3)) * (?r k)^2)
        \<longlongrightarrow> (mu / (4 * (1 - mu)^3)) * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const square_limit])
    then show ?thesis by simp
  qed
  have total_limit:
    "((\<lambda>k. (mu / (1 - mu)^2) * (?r k)^4 +
      (mu / (4 * (1 - mu)^3)) * (?r k)^2)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF first_term_limit second_term_limit] by simp
  have function_identity:
    "(\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k)) =
     (\<lambda>k. (mu / (1 - mu)^2) * (?r k)^4 +
      (mu / (4 * (1 - mu)^3)) * (?r k)^2)"
    by (rule ext)
      (rule curriculum_momentum_transfer_error_exact_general[OF mu_less_one])
  show ?thesis using total_limit function_identity by simp
qed
text \<open>curriculum_momentum_transfer_error_eventually_small_general: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>

lemma curriculum_momentum_transfer_error_eventually_small_general:
  assumes mu_less_one: "mu < 1" and margin_positive: "0 < G"
  shows "\<forall>\<^sub>F k in sequentially.
    momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k) < G"
proof -
  note eventual_upper = order_tendstoD(2)
    [OF curriculum_momentum_transfer_error_tendsto_zero_general[OF mu_less_one],
      of G]
  show ?thesis using eventual_upper margin_positive by simp
qed
text \<open>curriculum_tail_ratio_nonnegative: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma curriculum_tail_ratio_nonnegative:
  "0 \<le> curriculum_tail_ratio k"
  unfolding curriculum_tail_ratio_def
  using curriculum_population_positive[of k]
  by (intro divide_nonneg_nonneg) simp_all
text \<open>curriculum_tail_ratio_below_half: アンカーとテールの比率に関する恒等式または境界を示す。\<close>

lemma curriculum_tail_ratio_below_half:
  "curriculum_tail_ratio k < 1 / 2"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_at_least_four: "4 \<le> ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have inverse_at_most_quarter: "1 / ?K \<le> (1::real) / 4"
    by (rule frac_le) (use K_at_least_four in simp_all)
  show ?thesis using inverse_at_most_quarter
    by (simp add: curriculum_tail_ratio_exact)
qed
text \<open>curriculum_learning_rate_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_learning_rate_tendsto_zero:
  "(curriculum_learning_rate \<longlongrightarrow> 0) sequentially"
proof -
  have power_limit:
    "((\<lambda>k. curriculum_tail_ratio k ^ 4)
      \<longlongrightarrow> 0 ^ 4) sequentially"
    by (rule tendsto_power[OF curriculum_tail_ratio_tendsto_zero])
  have function_identity:
    "curriculum_learning_rate = (\<lambda>k. curriculum_tail_ratio k ^ 4)"
  proof (rule ext)
    fix k
    show "curriculum_learning_rate k = curriculum_tail_ratio k ^ 4"
      unfolding curriculum_learning_rate_def
      using curriculum_tail_ratio_exact[of k]
      by (simp add: power_divide)
  qed
  show ?thesis using power_limit function_identity by simp
qed
text \<open>curriculum_clean_metric_limits: リスクと AUC の極限をまとめて示す。\<close>

lemma curriculum_clean_metric_limits:
  "((\<lambda>k. 1 - curriculum_tail_ratio k) \<longlongrightarrow> 1) sequentially"
  "((\<lambda>k. 1 - curriculum_tail_ratio k ^ 2) \<longlongrightarrow> 1) sequentially"
  "((\<lambda>k. 2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2)
      \<longlongrightarrow> 0) sequentially"
proof -
  have square_limit:
    "((\<lambda>k. curriculum_tail_ratio k ^ 2)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_power[OF curriculum_tail_ratio_tendsto_zero, of 2] by simp
  have twice_limit:
    "((\<lambda>k. 2 * curriculum_tail_ratio k)
      \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const curriculum_tail_ratio_tendsto_zero,
        of 2]
    by simp
  show "((\<lambda>k. 1 - curriculum_tail_ratio k)
      \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const curriculum_tail_ratio_tendsto_zero,
        of 1]
    by simp
  show "((\<lambda>k. 1 - curriculum_tail_ratio k ^ 2)
      \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const square_limit, of 1] by simp
  show "((\<lambda>k. 2 * curriculum_tail_ratio k -
      curriculum_tail_ratio k ^ 2) \<longlongrightarrow> 0) sequentially"
    using tendsto_diff[OF twice_limit square_limit] by simp
qed
text \<open>curriculum_scalar_inversion_eventually: 十分大きな段階で成立する評価を示す。\<close>

theorem curriculum_scalar_inversion_eventually:
  "\<forall>\<^sub>F k in sequentially.
    clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)) =
      1 - curriculum_tail_ratio k \<and>
    clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)) =
      curriculum_tail_ratio k \<and>
    1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        {xs. clean_test_risk (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) = curriculum_tail_ratio k \<and>
          clean_test_auc (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
          clean_test_risk (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) <
            clean_test_risk (curriculum_tail_ratio k)
              (attack_state (curriculum_learning_rate k)
                (curriculum_anchor_count k) (curriculum_tail_count k)) \<and>
          clean_test_auc (curriculum_tail_ratio k)
              (attack_state (curriculum_learning_rate k)
                (curriculum_anchor_count k) (curriculum_tail_count k)) <
            clean_test_auc (curriculum_tail_ratio k)
              (binary_logistic_state (curriculum_learning_rate k)
                (real (curriculum_anchor_count k) / real (curriculum_population k))
                xs (curriculum_population k))}"
proof -
  note eventual_conditions = eventually_conj[OF curriculum_tail_takeover_eventually
      curriculum_random_margin_eventually_gt_one]
  show ?thesis
  proof (rule eventually_mono[OF eventual_conditions])
    fix k
    assume conditions:
      "ln (1 + real (curriculum_anchor_count k) *
        (exp (curriculum_learning_rate k) - 1)) + 1 <
        curriculum_learning_rate k * real (curriculum_tail_count k) /
          (1 + exp 1) \<and>
       1 < random_order_lower_margin
        (curriculum_learning_rate k) (curriculum_anchor_count k)
        (curriculum_tail_count k) (curriculum_population k)
        (curriculum_confidence k)"
    have takeover:
      "ln (1 + real (curriculum_anchor_count k) *
        (exp (curriculum_learning_rate k) - 1)) + 1 <
        curriculum_learning_rate k * real (curriculum_tail_count k) /
          (1 + exp 1)"
      using conditions by simp
    have random_margin_positive:
      "0 < random_order_lower_margin
        (curriculum_learning_rate k) (curriculum_anchor_count k)
        (curriculum_tail_count k) (curriculum_population k)
        (curriculum_confidence k)"
      using conditions by linarith
    have gamma_positive: "0 < (1::real)" by simp
    note result = finite_pool_order_only_inversion
      [where N="curriculum_population k"
        and m="curriculum_tail_count k"
        and n="curriculum_anchor_count k"
        and eta="curriculum_learning_rate k" and gamma=1
        and delta="curriculum_confidence k"
        and epsilon="curriculum_tail_ratio k",
       OF curriculum_population_positive curriculum_counts
          curriculum_tail_positive curriculum_tail_smaller
          curriculum_learning_rate_positive curriculum_learning_rate_at_most_four
          gamma_positive curriculum_confidence_positive
          curriculum_confidence_at_most_one curriculum_tail_ratio_nonnegative
          curriculum_tail_ratio_below_half takeover random_margin_positive]
    show "clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)) =
      1 - curriculum_tail_ratio k \<and>
      clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)) =
      curriculum_tail_ratio k \<and>
      1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        {xs. clean_test_risk (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) = curriculum_tail_ratio k \<and>
          clean_test_auc (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
          clean_test_risk (curriculum_tail_ratio k)
            (binary_logistic_state (curriculum_learning_rate k)
              (real (curriculum_anchor_count k) / real (curriculum_population k))
              xs (curriculum_population k)) <
            clean_test_risk (curriculum_tail_ratio k)
              (attack_state (curriculum_learning_rate k)
                (curriculum_anchor_count k) (curriculum_tail_count k)) \<and>
          clean_test_auc (curriculum_tail_ratio k)
              (attack_state (curriculum_learning_rate k)
                (curriculum_anchor_count k) (curriculum_tail_count k)) <
            clean_test_auc (curriculum_tail_ratio k)
              (binary_logistic_state (curriculum_learning_rate k)
                (real (curriculum_anchor_count k) / real (curriculum_population k))
                xs (curriculum_population k))}"
      using result(1) result(2) result(3) by blast
  qed
qed
text \<open>curriculum_attack_risk_tendsto_one: 対応する量が段階極限で 1 へ収束することを示す。\<close>

lemma curriculum_attack_risk_tendsto_one:
  "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (attack_state (curriculum_learning_rate k)
        (curriculum_anchor_count k) (curriculum_tail_count k)))
    \<longlongrightarrow> 1) sequentially"
proof -
  have eventual_identity:
    "\<forall>\<^sub>F k in sequentially.
      1 - curriculum_tail_ratio k =
      clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))"
    using curriculum_scalar_inversion_eventually
    by eventually_elim simp
  show ?thesis
    by (rule Lim_transform_eventually
        [OF curriculum_clean_metric_limits(1) eventual_identity])
qed
text \<open>curriculum_attack_auc_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_attack_auc_tendsto_zero:
  "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (attack_state (curriculum_learning_rate k)
        (curriculum_anchor_count k) (curriculum_tail_count k)))
    \<longlongrightarrow> 0) sequentially"
proof -
  have eventual_identity:
    "\<forall>\<^sub>F k in sequentially.
      curriculum_tail_ratio k =
      clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))"
    using curriculum_scalar_inversion_eventually
    by eventually_elim simp
  show ?thesis
    by (rule Lim_transform_eventually
        [OF curriculum_tail_ratio_tendsto_zero eventual_identity])
qed
text \<open>curriculum_realizable_inversion_eventually: 十分大きな段階で成立する評価を示す。\<close>

theorem curriculum_realizable_inversion_eventually:
  fixes xs_attack xs_random :: "nat \<Rightarrow> bool list"
  assumes attack_reference: "\<And>k. binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
  shows "\<forall>\<^sub>F k in sequentially.
    realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
    realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k)) = curriculum_tail_ratio k \<and>
    realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k)) =
      2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2 \<and>
    realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k)) =
      1 - curriculum_tail_ratio k ^ 2"
proof -
  have eventual_error:
    "\<forall>\<^sub>F k in sequentially.
      realizable_transfer_error (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (curriculum_population k) < 1"
    by (rule curriculum_realizable_transfer_error_eventually_small) simp
  show ?thesis
  proof (rule eventually_mono[OF eventual_error])
    fix k
    assume error_small:
      "realizable_transfer_error (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (curriculum_population k) < 1"
    have scale_nonzero: "curriculum_realizable_scale k \<noteq> 0"
      unfolding curriculum_realizable_scale_def
      using curriculum_scale_at_least_four[of k] by simp
    note result = realizable_inversion_transfer
      [where eta="curriculum_learning_rate k"
        and kappa="curriculum_realizable_scale k"
        and q="real (curriculum_anchor_count k) / real (curriculum_population k)"
        and xs_attack="xs_attack k" and xs_random="xs_random k"
        and N="curriculum_population k" and G_attack=1 and G_random=1
        and epsilon="curriculum_tail_ratio k",
       OF curriculum_learning_rate_positive curriculum_learning_rate_at_most_four
          scale_nonzero curriculum_population_positive attack_reference
          random_reference]
    show "realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
      realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k)) = curriculum_tail_ratio k \<and>
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k)
          (curriculum_population k)) =
        2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2 \<and>
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k)
          (curriculum_population k)) =
        1 - curriculum_tail_ratio k ^ 2"
      using result error_small by simp
  qed
qed
text \<open>curriculum_momentum_effective_step_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>

lemma curriculum_momentum_effective_step_tendsto_zero:
  assumes mu_less_one: "mu < 1"
  shows "((\<lambda>k. momentum_effective_step (curriculum_learning_rate k) mu)
    \<longlongrightarrow> 0) sequentially"
proof -
  have denominator_nonzero: "1 - mu \<noteq> 0"
    using mu_less_one by linarith
  have quotient_limit:
    "((\<lambda>k. curriculum_learning_rate k / (1 - mu))
      \<longlongrightarrow> 0 / (1 - mu)) sequentially"
    by (rule tendsto_divide[OF curriculum_learning_rate_tendsto_zero tendsto_const])
      (rule denominator_nonzero)
  show ?thesis using quotient_limit denominator_nonzero
    by (simp add: momentum_effective_step_def)
qed
text \<open>curriculum_momentum_inversion_eventually: 十分大きな段階で成立する評価を示す。\<close>

theorem curriculum_momentum_inversion_eventually:
  fixes mu :: real and xs_attack xs_random :: "nat \<Rightarrow> bool list"
  assumes mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and attack_reference: "\<And>k. binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
  shows "\<forall>\<^sub>F k in sequentially.
    clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
    clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k)) = curriculum_tail_ratio k \<and>
    clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k)) = curriculum_tail_ratio k \<and>
    clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k)) = 1 - curriculum_tail_ratio k"
proof -
  have effective_limit:
    "((\<lambda>k. momentum_effective_step (curriculum_learning_rate k) mu)
      \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_momentum_effective_step_tendsto_zero[OF mu_less_one])
  have eventual_effective_small:
    "\<forall>\<^sub>F k in sequentially.
      momentum_effective_step (curriculum_learning_rate k) mu < 4"
  proof -
    note eventual_upper = order_tendstoD(2)[OF effective_limit, of 4]
    show ?thesis using eventual_upper by simp
  qed
  have eventual_error:
    "\<forall>\<^sub>F k in sequentially.
      momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    by (rule curriculum_momentum_transfer_error_eventually_small_general
        [OF mu_less_one]) simp
  note eventual_conditions = eventually_conj[OF eventual_effective_small eventual_error]
  show ?thesis
  proof (rule eventually_mono[OF eventual_conditions])
    fix k
    assume conditions:
      "momentum_effective_step (curriculum_learning_rate k) mu < 4 \<and>
       momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    have effective_at_most_four:
      "momentum_effective_step (curriculum_learning_rate k) mu \<le> 4"
      using conditions by linarith
    note result = momentum_inversion_transfer
      [where eta="curriculum_learning_rate k" and mu=mu
        and q="real (curriculum_anchor_count k) / real (curriculum_population k)"
        and xs_attack="xs_attack k" and xs_random="xs_random k"
        and N="curriculum_population k" and G_attack=1 and G_random=1
        and epsilon="curriculum_tail_ratio k",
       OF curriculum_learning_rate_positive mu_nonnegative mu_less_one
          effective_at_most_four attack_reference random_reference]
    show "clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
      clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k)) = curriculum_tail_ratio k \<and>
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)) = curriculum_tail_ratio k \<and>
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k)) = 1 - curriculum_tail_ratio k"
      using result conditions by simp
  qed
qed
text \<open>curriculum_realizable_metric_limits: リスクと AUC の極限をまとめて示す。\<close>

theorem curriculum_realizable_metric_limits:
  fixes xs_attack xs_random :: "nat \<Rightarrow> bool list"
  assumes attack_reference: "\<And>k. binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
  shows "((\<lambda>k. realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)))
    \<longlongrightarrow> 1) sequentially"
    and "((\<lambda>k. realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)))
    \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)))
    \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)))
    \<longlongrightarrow> 1) sequentially"
proof -
  note identities = curriculum_realizable_inversion_eventually
    [OF attack_reference random_reference]
  show "((\<lambda>k. realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)))
    \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(1)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k =
      realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)))
    \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_tail_ratio_tendsto_zero])
    show "\<forall>\<^sub>F k in sequentially. curriculum_tail_ratio k =
      realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)))
    \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(3)])
    show "\<forall>\<^sub>F k in sequentially.
      2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2 =
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)))
    \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(2)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k ^ 2 =
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
qed
text \<open>curriculum_momentum_metric_limits: リスクと AUC の極限をまとめて示す。\<close>

theorem curriculum_momentum_metric_limits:
  fixes mu :: real and xs_attack xs_random :: "nat \<Rightarrow> bool list"
  assumes mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and attack_reference: "\<And>k. binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
  shows "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
    and "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
proof -
  note identities = curriculum_momentum_inversion_eventually
    [OF mu_nonnegative mu_less_one attack_reference random_reference]
  show "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(1)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k =
      clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_tail_ratio_tendsto_zero])
    show "\<forall>\<^sub>F k in sequentially. curriculum_tail_ratio k =
      clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_attack k) (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_tail_ratio_tendsto_zero])
    show "\<forall>\<^sub>F k in sequentially. curriculum_tail_ratio k =
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
  show "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (xs_random k) (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(1)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k =
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k))"
      using identities by eventually_elim simp
  qed
qed
text \<open>curriculum_random_inversion_event: ランダム順序でスカラー反転が起こる事象を定める。\<close>

definition curriculum_random_inversion_event :: "nat \<Rightarrow> bool list set" where
  "curriculum_random_inversion_event k =
    {xs. clean_test_risk (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          xs (curriculum_population k)) = curriculum_tail_ratio k \<and>
      clean_test_auc (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          xs (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
      clean_test_risk (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          xs (curriculum_population k)) <
        clean_test_risk (curriculum_tail_ratio k)
          (attack_state (curriculum_learning_rate k)
            (curriculum_anchor_count k) (curriculum_tail_count k)) \<and>
      clean_test_auc (curriculum_tail_ratio k)
          (attack_state (curriculum_learning_rate k)
            (curriculum_anchor_count k) (curriculum_tail_count k)) <
        clean_test_auc (curriculum_tail_ratio k)
          (binary_logistic_state (curriculum_learning_rate k)
            (real (curriculum_anchor_count k) / real (curriculum_population k))
            xs (curriculum_population k))}"
text \<open>curriculum_random_inversion_probability_eventually: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_random_inversion_probability_eventually:
  "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
    uniform_probability
      (binary_orders (curriculum_anchor_count k) (curriculum_population k))
      (curriculum_random_inversion_event k)"
  using curriculum_scalar_inversion_eventually
  unfolding curriculum_random_inversion_event_def
  by eventually_elim blast
text \<open>order_only_inversion_conditional_asymptotic: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem order_only_inversion_conditional_asymptotic:
  fixes mu :: real and xs_attack xs_random :: "nat \<Rightarrow> bool list"
  assumes mu_nonnegative: "0 \<le> mu"
    and mu_less_one: "mu < 1"
    and realizable_attack_reference: "\<And>k. binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and realizable_random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (curriculum_learning_rate k)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
    and momentum_attack_reference: "\<And>k. binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_attack k) (curriculum_population k) \<le> -1"
    and momentum_random_reference: "\<And>k. 1 \<le> binary_logistic_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (real (curriculum_anchor_count k) / real (curriculum_population k))
      (xs_random k) (curriculum_population k)"
  shows "(curriculum_tail_ratio \<longlongrightarrow> 0) sequentially"
    and "(curriculum_confidence \<longlongrightarrow> 0) sequentially"
    and "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        (curriculum_random_inversion_event k)"
    and "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)),
       clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))))
      \<longlongrightarrow> (1, 0)) sequentially"
    and "((\<lambda>k.
      (realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)),
       realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))))
      \<longlongrightarrow> (1, 0, 0, 1)) sequentially"
    and "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)),
       clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k))))
      \<longlongrightarrow> (1, 0, 0, 1)) sequentially"
    and "((\<lambda>k. realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k))
      \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
proof -
  note realizable_limits = curriculum_realizable_metric_limits
    [OF realizable_attack_reference realizable_random_reference]
  note momentum_limits = curriculum_momentum_metric_limits
    [OF mu_nonnegative mu_less_one momentum_attack_reference
        momentum_random_reference]
  show "(curriculum_tail_ratio \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_tail_ratio_tendsto_zero)
  show "(curriculum_confidence \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_confidence_tendsto_zero)
  show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        (curriculum_random_inversion_event k)"
    by (rule curriculum_random_inversion_probability_eventually)
  show "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)),
       clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))))
      \<longlongrightarrow> (1, 0)) sequentially"
    by (intro tendsto_Pair curriculum_attack_risk_tendsto_one
        curriculum_attack_auc_tendsto_zero)
  show "((\<lambda>k.
      (realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)),
       realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_attack k) (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (xs_random k) (curriculum_population k))))
      \<longlongrightarrow> (1, 0, 0, 1)) sequentially"
    by (intro tendsto_Pair realizable_limits)
  show "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)),
       clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_attack k) (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (xs_random k) (curriculum_population k))))
      \<longlongrightarrow> (1, 0, 0, 1)) sequentially"
    by (intro tendsto_Pair momentum_limits)
  show "((\<lambda>k. realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k))
      \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_realizable_transfer_error_tendsto_zero)
  show "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) mu
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_momentum_transfer_error_tendsto_zero_general
        [OF mu_less_one])
qed
text \<open>curriculum_explicit_realizable_attack_metrics_eventually: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_explicit_realizable_attack_metrics_eventually:
  shows "\<forall>\<^sub>F k in sequentially.
    realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
    realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)) =
      2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2"
proof -
  have eventual_error: "\<forall>\<^sub>F k in sequentially.
      realizable_transfer_error (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (curriculum_population k) < 1"
    by (rule curriculum_realizable_transfer_error_eventually_small) simp
  note conditions = eventually_conj[OF curriculum_attack_margin_eventually
      eventual_error]
  show ?thesis
  proof (rule eventually_mono[OF conditions])
    fix k
    assume condition:
      "attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k) < -1 \<and>
       realizable_transfer_error (curriculum_learning_rate k)
          (curriculum_realizable_scale k) (curriculum_population k) < 1"
    let ?xs = "attack_order (curriculum_anchor_count k)
      (curriculum_tail_count k)"
    have count_sum: "curriculum_anchor_count k + curriculum_tail_count k =
        curriculum_population k"
      using curriculum_counts[of k] by simp
    have reference:
      "binary_logistic_state (curriculum_learning_rate k)
        (real (curriculum_anchor_count k) / real (curriculum_population k))
        ?xs (curriculum_population k) \<le> -1"
      using binary_logistic_state_attack_order
        [of "curriculum_learning_rate k"
          "real (curriculum_anchor_count k) / real (curriculum_population k)"
          "curriculum_anchor_count k" "curriculum_tail_count k"]
        count_sum condition by simp
    have scale_nonzero: "curriculum_realizable_scale k \<noteq> 0"
      unfolding curriculum_realizable_scale_def
      using curriculum_scale_at_least_four[of k] by simp
    have u_positive: "0 < realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) ?xs (curriculum_population k)"
      by (rule realizable_u_state_positive
          [OF curriculum_learning_rate_positive scale_nonzero
            curriculum_population_positive])
    have dominance:
      "realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k) <
       - realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k)"
      by (rule realizable_negative_dominance_transfer
          [OF order_less_imp_le[OF curriculum_learning_rate_positive]
            curriculum_learning_rate_at_most_four reference])
        (use condition in simp)
    show "realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k)) =
          1 - curriculum_tail_ratio k \<and>
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k) ?xs (curriculum_population k)) =
          2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2"
    proof
      show "realizable_test_risk (curriculum_tail_ratio k)
          (realizable_a_state (curriculum_learning_rate k)
            (curriculum_realizable_scale k) ?xs (curriculum_population k))
          (realizable_u_state (curriculum_learning_rate k)
            (curriculum_realizable_scale k) ?xs (curriculum_population k)) =
            1 - curriculum_tail_ratio k"
        by (rule realizable_test_risk_negative[OF u_positive dominance])
      show "realizable_test_auc (curriculum_tail_ratio k)
          (realizable_a_state (curriculum_learning_rate k)
            (curriculum_realizable_scale k) ?xs (curriculum_population k))
          (realizable_u_state (curriculum_learning_rate k)
            (curriculum_realizable_scale k) ?xs (curriculum_population k)) =
            2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2"
        by (rule realizable_test_auc_attack[OF u_positive dominance])
    qed
  qed
qed
text \<open>curriculum_explicit_realizable_attack_metric_limits: リスクと AUC の極限をまとめて示す。\<close>

lemma curriculum_explicit_realizable_attack_metric_limits:
  "((\<lambda>k.
    (realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)),
     realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
proof (intro tendsto_Pair)
  show "((\<lambda>k. realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(1)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k =
      realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))"
      using curriculum_explicit_realizable_attack_metrics_eventually
      by eventually_elim simp
  qed
  show "((\<lambda>k. realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k)
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(3)])
    show "\<forall>\<^sub>F k in sequentially.
      2 * curriculum_tail_ratio k - curriculum_tail_ratio k ^ 2 =
      realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))"
      using curriculum_explicit_realizable_attack_metrics_eventually
      by eventually_elim simp
  qed
qed
text \<open>curriculum_realizable_random_benign_event: 実現可能モデルで正常なリスクと AUC が得られる順序事象を定める。\<close>

definition curriculum_realizable_random_benign_event :: "nat \<Rightarrow> bool list set" where
  "curriculum_realizable_random_benign_event k = {xs.
    realizable_test_risk (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) xs (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) xs (curriculum_population k)) =
      curriculum_tail_ratio k \<and>
    realizable_test_auc (curriculum_tail_ratio k)
      (realizable_a_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) xs (curriculum_population k))
      (realizable_u_state (curriculum_learning_rate k)
        (curriculum_realizable_scale k) xs (curriculum_population k)) =
      1 - curriculum_tail_ratio k ^ 2}"
text \<open>curriculum_realizable_random_benign_probability: 実現可能な正常事象の一様確率を定める。\<close>

definition curriculum_realizable_random_benign_probability :: "nat \<Rightarrow> real" where
  "curriculum_realizable_random_benign_probability k = uniform_probability
    (binary_orders (curriculum_anchor_count k) (curriculum_population k))
    (curriculum_realizable_random_benign_event k)"
text \<open>curriculum_realizable_random_probability_eventually: 十分大きな段階で成立する評価を示す。\<close>

lemma curriculum_realizable_random_probability_eventually:
  "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
    curriculum_realizable_random_benign_probability k"
proof -
  have eventual_error: "\<forall>\<^sub>F k in sequentially.
      realizable_transfer_error (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (curriculum_population k) < 1"
    by (rule curriculum_realizable_transfer_error_eventually_small) simp
  note conditions = eventually_conj[OF curriculum_random_margin_eventually_gt_one
    eventual_error]
  show ?thesis
  proof (rule eventually_mono[OF conditions])
    fix k
    assume condition: "1 < random_order_lower_margin
        (curriculum_learning_rate k) (curriculum_anchor_count k)
        (curriculum_tail_count k) (curriculum_population k)
        (curriculum_confidence k) \<and>
      realizable_transfer_error (curriculum_learning_rate k)
        (curriculum_realizable_scale k) (curriculum_population k) < 1"
    let ?N = "curriculum_population k"
    let ?m = "curriculum_tail_count k"
    let ?n = "curriculum_anchor_count k"
    let ?eta = "curriculum_learning_rate k"
    let ?delta = "curriculum_confidence k"
    let ?epsilon = "curriculum_tail_ratio k"
    let ?kappa = "curriculum_realizable_scale k"
    let ?margin = "random_order_lower_margin ?eta ?n ?m ?N ?delta"
    let ?bounded = "{xs. ?margin \<le>
      binary_logistic_state ?eta (real ?n / real ?N) xs ?N}"
    have confidence: "1 - ?delta \<le> uniform_probability
        (binary_orders ?n ?N) ?bounded"
      by (rule uniform_binary_order_logistic_confidence[OF
        curriculum_population_positive curriculum_counts
        curriculum_tail_positive curriculum_tail_smaller
        order_less_imp_le[OF curriculum_learning_rate_positive]
        curriculum_learning_rate_at_most_four curriculum_confidence_positive
        curriculum_confidence_at_most_one])
    have kappa_nonzero: "?kappa \<noteq> 0"
      unfolding curriculum_realizable_scale_def
      using curriculum_scale_at_least_four[of k] by simp
    have event_subset: "?bounded \<subseteq> curriculum_realizable_random_benign_event k"
    proof
      fix xs
      assume member: "xs \<in> ?bounded"
      have reference_margin: "1 \<le> binary_logistic_state ?eta
          (real ?n / real ?N) xs ?N"
        using member condition by simp
      note metrics = realizable_random_metric_transfer[OF
        curriculum_learning_rate_positive curriculum_learning_rate_at_most_four
        kappa_nonzero curriculum_population_positive reference_margin,
        of ?epsilon]
      have risk: "realizable_test_risk ?epsilon
          (realizable_a_state ?eta ?kappa xs ?N)
          (realizable_u_state ?eta ?kappa xs ?N) = ?epsilon"
        by (rule metrics(1)) (use condition in simp)
      have auc: "realizable_test_auc ?epsilon
          (realizable_a_state ?eta ?kappa xs ?N)
          (realizable_u_state ?eta ?kappa xs ?N) = 1 - ?epsilon ^ 2"
        by (rule metrics(2)) (use condition in simp)
      show "xs \<in> curriculum_realizable_random_benign_event k"
        unfolding curriculum_realizable_random_benign_event_def
        using risk auc by simp
    qed
    have probability_mono: "uniform_probability (binary_orders ?n ?N) ?bounded \<le>
        uniform_probability (binary_orders ?n ?N)
          (curriculum_realizable_random_benign_event k)"
      by (rule uniform_probability_mono[OF finite_binary_orders event_subset])
    show "1 - curriculum_confidence k \<le>
        curriculum_realizable_random_benign_probability k"
      unfolding curriculum_realizable_random_benign_probability_def
      using confidence probability_mono by linarith
  qed
qed
text \<open>curriculum_realizable_random_benign_probability_tendsto_one: 対応する量が段階極限で 1 へ収束することを示す。\<close>

lemma curriculum_realizable_random_benign_probability_tendsto_one:
  "(curriculum_realizable_random_benign_probability \<longlongrightarrow> 1) sequentially"
proof -
  have lower_limit: "((\<lambda>k. 1 - curriculum_confidence k) \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const curriculum_confidence_tendsto_zero] by simp
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      curriculum_realizable_random_benign_probability k \<le> 1"
    by (intro always_eventually allI)
      (simp add: curriculum_realizable_random_benign_probability_def
        uniform_probability_le_one[OF finite_binary_orders])
  show ?thesis by (rule tendsto_sandwich[OF
    curriculum_realizable_random_probability_eventually upper_bound
    lower_limit tendsto_const])
qed
text \<open>order_only_inversion_complete_asymptotic: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>

theorem order_only_inversion_complete_asymptotic:
  shows "(curriculum_tail_ratio \<longlongrightarrow> 0) sequentially"
    and "(curriculum_confidence \<longlongrightarrow> 0) sequentially"
    and "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        (curriculum_random_inversion_event k)"
    and "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
    and "((\<lambda>k.
      (realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
    and "\<And>k xs q. momentum_w_state (curriculum_learning_rate k) 0 xs
      (curriculum_population k) =
      binary_logistic_state (curriculum_learning_rate k) q xs
        (curriculum_population k)"
    and "((\<lambda>k. realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k))
      \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) 0
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
proof -
  show "(curriculum_tail_ratio \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_tail_ratio_tendsto_zero)
  show "(curriculum_confidence \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_confidence_tendsto_zero)
  show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_confidence k \<le>
      uniform_probability
        (binary_orders (curriculum_anchor_count k) (curriculum_population k))
        (curriculum_random_inversion_event k)"
    by (rule curriculum_random_inversion_probability_eventually)
  show "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
  proof (rule Lim_transform_eventually)
    show "((\<lambda>k.
      (clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)),
       clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))))
      \<longlongrightarrow> (1, 0)) sequentially"
      by (intro tendsto_Pair curriculum_attack_risk_tendsto_one
          curriculum_attack_auc_tendsto_zero)
    show "\<forall>\<^sub>F k in sequentially.
      (clean_test_risk (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k)),
       clean_test_auc (curriculum_tail_ratio k)
        (attack_state (curriculum_learning_rate k)
          (curriculum_anchor_count k) (curriculum_tail_count k))) =
      (clean_test_risk (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)),
       clean_test_auc (curriculum_tail_ratio k)
        (binary_logistic_state (curriculum_learning_rate k)
          (real (curriculum_anchor_count k) / real (curriculum_population k))
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)))"
      apply (rule always_eventually)
      proof
        fix k
        have count_sum:
          "curriculum_anchor_count k + curriculum_tail_count k =
            curriculum_population k"
          using curriculum_counts[of k] by simp
        have state_eq:
          "binary_logistic_state (curriculum_learning_rate k)
            (real (curriculum_anchor_count k) / real (curriculum_population k))
            (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
            (curriculum_population k) =
           attack_state (curriculum_learning_rate k)
            (curriculum_anchor_count k) (curriculum_tail_count k)"
          using binary_logistic_state_attack_order
            [of "curriculum_learning_rate k"
              "real (curriculum_anchor_count k) / real (curriculum_population k)"
              "curriculum_anchor_count k" "curriculum_tail_count k"]
            count_sum by simp
        show "(clean_test_risk (curriculum_tail_ratio k)
          (attack_state (curriculum_learning_rate k)
            (curriculum_anchor_count k) (curriculum_tail_count k)),
         clean_test_auc (curriculum_tail_ratio k)
          (attack_state (curriculum_learning_rate k)
            (curriculum_anchor_count k) (curriculum_tail_count k))) =
        (clean_test_risk (curriculum_tail_ratio k)
          (binary_logistic_state (curriculum_learning_rate k)
            (real (curriculum_anchor_count k) / real (curriculum_population k))
            (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
            (curriculum_population k)),
         clean_test_auc (curriculum_tail_ratio k)
          (binary_logistic_state (curriculum_learning_rate k)
            (real (curriculum_anchor_count k) / real (curriculum_population k))
            (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
            (curriculum_population k)))"
          using state_eq by simp
      qed
  qed
  show "((\<lambda>k.
      (realizable_test_risk (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)),
       realizable_test_auc (curriculum_tail_ratio k)
        (realizable_a_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))
        (realizable_u_state (curriculum_learning_rate k)
          (curriculum_realizable_scale k)
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
    by (rule curriculum_explicit_realizable_attack_metric_limits)
  show "\<And>k xs q. momentum_w_state (curriculum_learning_rate k) 0 xs
      (curriculum_population k) =
      binary_logistic_state (curriculum_learning_rate k) q xs
        (curriculum_population k)"
    by (rule momentum_zero_reference_exact
        [OF order_less_imp_le[OF curriculum_learning_rate_positive]
          curriculum_learning_rate_at_most_four])
  show "((\<lambda>k. realizable_transfer_error (curriculum_learning_rate k)
      (curriculum_realizable_scale k) (curriculum_population k))
      \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_realizable_transfer_error_tendsto_zero)
  show "((\<lambda>k. momentum_transfer_error (curriculum_learning_rate k) 0
      (curriculum_population k)) \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_momentum_transfer_error_tendsto_zero_general) simp
qed
text \<open>linearly_realizable: マージン列が一つの線形重みで正になる条件を定める。\<close>

definition linearly_realizable :: "real list \<Rightarrow> bool" where
  "linearly_realizable margins \<longleftrightarrow>
    (\<exists>w. \<forall>z \<in> set margins. 0 < w * z)"
text \<open>uniform_margin_realizable: 有界重みで一様マージンを保証する条件を定める。\<close>

definition uniform_margin_realizable ::
    "real \<Rightarrow> real \<Rightarrow> real list \<Rightarrow> bool" where
  "uniform_margin_realizable gamma B margins \<longleftrightarrow>
    (\<exists>w. abs w \<le> B \<and> (\<forall>z \<in> set margins. gamma \<le> w * z))"
text \<open>uniform_margin_realizable_imp_linearly_realizable: 更新後の分類マージンを評価する。\<close>

lemma uniform_margin_realizable_imp_linearly_realizable:
  assumes gamma_positive: "0 < gamma"
    and uniform: "uniform_margin_realizable gamma B margins"
  shows "linearly_realizable margins"
proof -
  obtain w where witness:
      "abs w \<le> B" "\<forall>z \<in> set margins. gamma \<le> w * z"
    using uniform unfolding uniform_margin_realizable_def by blast
  show ?thesis
    unfolding linearly_realizable_def
  proof (intro exI ballI)
    fix z
    assume "z \<in> set margins"
    then have "gamma \<le> w * z" using witness by blast
    then show "0 < w * z" using gamma_positive by linarith
  qed
qed
text \<open>inversion_exponent_regime: スケーリング指数が反転に適する領域を定める。\<close>

definition inversion_exponent_regime :: "real \<Rightarrow> real \<Rightarrow> bool" where
  "inversion_exponent_regime a b \<longleftrightarrow> a / 2 < b \<and> b < a - 1"
text \<open>inversion_exponent_regime_conditions: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>
lemma inversion_exponent_regime_conditions:
  assumes regime: "inversion_exponent_regime a b"
  shows "2 < a" "0 < b - a / 2" "0 < a - 1 - b"
  using regime unfolding inversion_exponent_regime_def by linarith+

text \<open>admissible_momentum_schedule: 全段階で 0 以上 1 未満となるモメンタム列を定める。\<close>
definition admissible_momentum_schedule :: "(nat \<Rightarrow> real) \<Rightarrow> bool" where
  "admissible_momentum_schedule mu \<longleftrightarrow>
    (\<forall>k. 0 \<le> mu k \<and> mu k < 1)"

text \<open>varying_momentum_transfer_eventually_small: 十分大きな段階で成立する評価を示す。\<close>
lemma varying_momentum_transfer_eventually_small:
  assumes error_limit:
      "((\<lambda>k. momentum_transfer_error (eta k) (mu k) (N k))
        \<longlongrightarrow> 0) sequentially"
    and margin_positive: "0 < G"
  shows "\<forall>\<^sub>F k in sequentially.
    momentum_transfer_error (eta k) (mu k) (N k) < G"
proof -
  note eventual_upper = order_tendstoD(2)[OF error_limit, of G]
  show ?thesis using eventual_upper margin_positive by simp
qed

text \<open>normed_perturbation_transfer: 理想更新と摂動付き更新の差を評価し、性質を移送する。\<close>
lemma normed_perturbation_transfer:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes nonexpansive: "norm (F x - F y) \<le> norm (x - y)"
  shows "norm ((F x + e) - F y) \<le> norm (x - y) + norm e"
proof -
  have identity: "(F x + e) - F y = (F x - F y) + e" by simp
  have triangle: "norm ((F x - F y) + e) \<le> norm (F x - F y) + norm e"
    by (rule norm_triangle_ineq)
  show ?thesis unfolding identity using triangle nonexpansive by linarith
qed

section \<open>Integer power-law families\<close>


text \<open>power_population: 基本スケールの指数 a による母集団サイズを定める。\<close>
definition power_population :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "power_population a k = curriculum_scale k ^ a"

text \<open>power_tail: 基本スケールの指数 c によるテールサイズを定める。\<close>
definition power_tail :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "power_tail c k = curriculum_scale k ^ c"

text \<open>power_learning_rate: 基本スケールの指数 b による学習率を定める。\<close>
definition power_learning_rate :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "power_learning_rate b k = 1 / real (curriculum_scale k) ^ b"

text \<open>inverse_curriculum_power_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma inverse_curriculum_power_tendsto_zero:
  assumes exponent_positive: "0 < d"
  shows "((\<lambda>k. 1 / real (curriculum_scale k) ^ d) \<longlongrightarrow> 0) sequentially"
proof -
  have base: "((\<lambda>k. 1 / real (curriculum_scale k)) \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have powered:
      "((\<lambda>k. (1 / real (curriculum_scale k)) ^ d) \<longlongrightarrow> 0 ^ d) sequentially"
    by (rule tendsto_power[OF base])
  have zero_power: "(0::real) ^ d = 0"
    using exponent_positive by simp
  have powered_zero:
      "((\<lambda>k. (1 / real (curriculum_scale k)) ^ d) \<longlongrightarrow> 0) sequentially"
    using powered unfolding zero_power .
  have function_identity:
      "(\<lambda>k. 1 / real (curriculum_scale k) ^ d) =
       (\<lambda>k. (1 / real (curriculum_scale k)) ^ d)"
    by (rule ext) (simp add: power_divide)
  show ?thesis
    unfolding function_identity
    by (fact powered_zero)
qed

text \<open>power_law_scaling: 冪スケーリング族の対応する漸近性質を示す。\<close>
theorem power_law_scaling:
  assumes noise_condition: "a < 2 * b"
    and takeover_condition: "b < c"
    and vanishing_tail_condition: "c < a"
  shows "((\<lambda>k. real (power_tail c k) / real (power_population a k))
      \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. (power_learning_rate b k)^2 *
      real (power_population a k)) \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. 1 / (power_learning_rate b k * real (power_tail c k)))
      \<longlongrightarrow> 0) sequentially"
proof -
  have ratio_identity:
    "1 / x ^ (n - m) = x ^ m / x ^ n"
    if x_nonzero: "x \<noteq> (0::real)" and exponent_order: "m \<le> n"
    for x m n
  proof -
    have exponent_sum: "m + (n - m) = n"
      using exponent_order by simp
    have product: "x ^ m * x ^ (n - m) = x ^ n"
    proof -
      have "x ^ m * x ^ (n - m) = x ^ (m + (n - m))"
        by (rule power_add[symmetric])
      also have "\<dots> = x ^ n"
        unfolding exponent_sum ..
      finally show ?thesis .
    qed
    show ?thesis
      using x_nonzero product by (simp add: field_simps)
  qed
  have ac: "0 < a - c" using vanishing_tail_condition by simp
  have ba: "0 < 2 * b - a" using noise_condition by simp
  have cb: "0 < c - b" using takeover_condition by simp
  show "((\<lambda>k. real (power_tail c k) / real (power_population a k))
      \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF inverse_curriculum_power_tendsto_zero[OF ac]])
    show "\<forall>\<^sub>F k in sequentially.
      1 / real (curriculum_scale k) ^ (a - c) =
      real (power_tail c k) / real (power_population a k)"
    proof (rule always_eventually, rule allI)
      fix k
      have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
        using curriculum_scale_at_least_four[of k] by simp
      show "1 / real (curriculum_scale k) ^ (a - c) =
        real (power_tail c k) / real (power_population a k)"
        unfolding power_tail_def power_population_def of_nat_power
        by (rule ratio_identity[OF scale_nonzero])
          (use vanishing_tail_condition in simp)
    qed
  qed
  show "((\<lambda>k. (power_learning_rate b k)^2 *
      real (power_population a k)) \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF inverse_curriculum_power_tendsto_zero[OF ba]])
    show "\<forall>\<^sub>F k in sequentially.
      1 / real (curriculum_scale k) ^ (2 * b - a) =
      (power_learning_rate b k)^2 * real (power_population a k)"
    proof (rule always_eventually, rule allI)
      fix k
      let ?K = "real (curriculum_scale k)"
      have scale_nonzero: "?K \<noteq> 0"
        using curriculum_scale_at_least_four[of k] by simp
      have ratio: "1 / ?K ^ (2 * b - a) = ?K ^ a / ?K ^ (2 * b)"
        by (rule ratio_identity[OF scale_nonzero])
          (use noise_condition in simp)
      have square_power: "(?K ^ b)^2 = ?K ^ (2 * b)"
      proof -
        have "(?K ^ b)^2 = ?K ^ (b * 2)"
          by (rule power_mult[symmetric])
        also have "\<dots> = ?K ^ (2 * b)"
          by (simp add: mult.commute)
        finally show ?thesis .
      qed
      show "1 / ?K ^ (2 * b - a) =
        (power_learning_rate b k)^2 * real (power_population a k)"
        unfolding power_learning_rate_def power_population_def of_nat_power
        using ratio square_power scale_nonzero by (simp add: field_simps)
    qed
  qed
  show "((\<lambda>k. 1 / (power_learning_rate b k * real (power_tail c k)))
      \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF inverse_curriculum_power_tendsto_zero[OF cb]])
    show "\<forall>\<^sub>F k in sequentially.
      1 / real (curriculum_scale k) ^ (c - b) =
      1 / (power_learning_rate b k * real (power_tail c k))"
    proof (rule always_eventually, rule allI)
      fix k
      let ?K = "real (curriculum_scale k)"
      have scale_nonzero: "?K \<noteq> 0"
        using curriculum_scale_at_least_four[of k] by simp
      have ratio: "1 / ?K ^ (c - b) = ?K ^ b / ?K ^ c"
        by (rule ratio_identity[OF scale_nonzero])
          (use takeover_condition in simp)
      show "1 / ?K ^ (c - b) =
        1 / (power_learning_rate b k * real (power_tail c k))"
        unfolding power_learning_rate_def power_tail_def of_nat_power
        using ratio scale_nonzero by (simp add: field_simps)
    qed
  qed
qed
text \<open>power_law_anchor_tail_scaling: 冪スケーリング族の対応する漸近性質を示す。\<close>
theorem power_law_anchor_tail_scaling:
  assumes noise_condition: "a < 2 * b"
    and takeover_condition: "b + 1 < a"
  shows "((\<lambda>k. real (power_tail (a - 1) k) / real (power_population a k))
      \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. (power_learning_rate b k)^2 *
      real (power_population a k)) \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. 1 / (power_learning_rate b k * real (power_tail (a - 1) k)))
      \<longlongrightarrow> 0) sequentially"
proof -
  have tail_below_population: "a - 1 < a"
    using takeover_condition by simp
  have rate_below_tail: "b < a - 1"
    using takeover_condition by simp
  show "((\<lambda>k. real (power_tail (a - 1) k) / real (power_population a k))
      \<longlongrightarrow> 0) sequentially"
    by (rule power_law_scaling(1)[OF noise_condition rate_below_tail
          tail_below_population])
  show "((\<lambda>k. (power_learning_rate b k)^2 *
      real (power_population a k)) \<longlongrightarrow> 0) sequentially"
    by (rule power_law_scaling(2)[OF noise_condition rate_below_tail
          tail_below_population])
  show "((\<lambda>k. 1 / (power_learning_rate b k * real (power_tail (a - 1) k)))
      \<longlongrightarrow> 0) sequentially"
    by (rule power_law_scaling(3)[OF noise_condition rate_below_tail
          tail_below_population])
qed

text \<open>power_law_6_4_scaling: 冪スケーリング族の対応する漸近性質を示す。\<close>
corollary power_law_6_4_scaling:
  "((\<lambda>k. real (power_tail 5 k) / real (power_population 6 k))
      \<longlongrightarrow> 0) sequentially"
  "((\<lambda>k. (power_learning_rate 4 k)^2 *
      real (power_population 6 k)) \<longlongrightarrow> 0) sequentially"
  "((\<lambda>k. 1 / (power_learning_rate 4 k * real (power_tail 5 k)))
      \<longlongrightarrow> 0) sequentially"
  using power_law_anchor_tail_scaling[of 6 4] by simp_all


text \<open>power_anchor: 母集団から冪テールを除いたアンカーサイズを定める。\<close>
definition power_anchor :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "power_anchor a c k = power_population a k - power_tail c k"

text \<open>power_confidence: 冪スケーリングの信頼度誤差を定める。\<close>
definition power_confidence :: "nat \<Rightarrow> real" where
  "power_confidence k = 1 / real (curriculum_scale k) ^ 2"

text \<open>power_tail_ratio: 冪スケーリングのテール比率を定める。\<close>
definition power_tail_ratio :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "power_tail_ratio a c k =
    real (power_tail c k) / real (power_population a k)"

text \<open>power_tail_le_population: カリキュラムの個数または母集団分解を整理する。\<close>
lemma power_tail_le_population:
  assumes "c < a"
  shows "power_tail c k \<le> power_population a k"
proof -
  have K_ge_one: "1 \<le> curriculum_scale k"
    using curriculum_scale_at_least_four[of k] by simp
  have gap: "c + (a - c) = a" using assms by simp
  have gap_power: "1 \<le> curriculum_scale k ^ (a - c)"
    by (rule one_le_power[OF K_ge_one])
  have raw: "curriculum_scale k ^ c \<le> curriculum_scale k ^ a"
  proof -
    have "curriculum_scale k ^ c \<le>
        curriculum_scale k ^ c * curriculum_scale k ^ (a - c)"
      using gap_power by simp
    also have "\<dots> = curriculum_scale k ^ (c + (a - c))"
      by (rule power_add[symmetric])
    also have "\<dots> = curriculum_scale k ^ a" using gap by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding power_tail_def power_population_def by (rule raw)
qed

text \<open>power_counts: カリキュラムの個数または母集団分解を整理する。\<close>
lemma power_counts:
  assumes "c < a"
  shows "power_tail c k + power_anchor a c k = power_population a k"
  unfolding power_anchor_def using power_tail_le_population[OF assms] by simp

text \<open>power_population_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma power_population_positive: "0 < power_population a k"
  unfolding power_population_def
  using curriculum_scale_at_least_four[of k] by simp

text \<open>power_tail_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma power_tail_positive: "0 < power_tail c k"
  unfolding power_tail_def
  using curriculum_scale_at_least_four[of k] by simp

text \<open>power_learning_rate_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma power_learning_rate_positive: "0 < power_learning_rate b k"
  unfolding power_learning_rate_def
  using curriculum_scale_at_least_four[of k] by simp

text \<open>power_confidence_positive: 対象量が正であること、または正側の評価を示す。\<close>
lemma power_confidence_positive: "0 < power_confidence k"
  unfolding power_confidence_def
  using curriculum_scale_at_least_four[of k] by simp

text \<open>power_confidence_at_most_one: 対象量の上界を示す。\<close>
lemma power_confidence_at_most_one: "power_confidence k \<le> 1"
proof -
  have "1 \<le> real (curriculum_scale k) ^ 2"
    using curriculum_scale_at_least_four[of k] by simp
  have "1 / real (curriculum_scale k) ^ 2 \<le> (1::real) / 1"
    by (rule frac_le) (use \<open>1 \<le> real (curriculum_scale k) ^ 2\<close> in simp_all)
  then show ?thesis unfolding power_confidence_def by simp
qed

text \<open>power_confidence_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_confidence_tendsto_zero:
  "(power_confidence \<longlongrightarrow> 0) sequentially"
  unfolding power_confidence_def
  by (rule inverse_curriculum_power_tendsto_zero) simp

text \<open>power_population_factorization: カリキュラムの個数または母集団分解を整理する。\<close>
lemma power_population_factorization:
  assumes tail_below_population: "c < a"
  shows "power_population a k =
    power_tail c k * curriculum_scale k ^ (a - c)"
proof -
  have exponent: "c + (a - c) = a"
    using tail_below_population by simp
  have raw: "curriculum_scale k ^ a =
      curriculum_scale k ^ c * curriculum_scale k ^ (a - c)"
  proof -
    have "curriculum_scale k ^ a = curriculum_scale k ^ (c + (a - c))"
      using exponent by simp
    also have "\<dots> = curriculum_scale k ^ c * curriculum_scale k ^ (a - c)"
      by (rule power_add)
    finally show ?thesis .
  qed
  show ?thesis unfolding power_population_def power_tail_def by (rule raw)
qed

text \<open>power_tail_ratio_exact: アンカーとテールの比率に関する恒等式または境界を示す。\<close>
lemma power_tail_ratio_exact:
  assumes tail_below_population: "c < a"
  shows "power_tail_ratio a c k =
    1 / real (curriculum_scale k) ^ (a - c)"
proof -
  have scale_nonzero: "real (curriculum_scale k) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have tail_nonzero: "real (power_tail c k) \<noteq> 0"
    using power_tail_positive[of c k] by simp
  have cast_factorization:
    "real (power_population a k) = real (power_tail c k) *
      real (curriculum_scale k) ^ (a - c)"
    using power_population_factorization[OF tail_below_population, of k]
    by simp
  show ?thesis
    unfolding power_tail_ratio_def
    using cast_factorization tail_nonzero scale_nonzero
    by (simp add: field_simps)
qed

text \<open>power_tail_ratio_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_tail_ratio_tendsto_zero:
  assumes tail_below_population: "c < a"
  shows "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
  using inverse_curriculum_power_tendsto_zero[of "a - c"]
    tail_below_population
  by (simp add: power_tail_ratio_exact)

text \<open>power_tail_less_anchor: 冪スケーリング族の対応する漸近性質を示す。\<close>
lemma power_tail_less_anchor:
  assumes tail_below_population: "c < a"
  shows "power_tail c k < power_anchor a c k"
proof -
  let ?K = "curriculum_scale k"
  have gap_positive: "0 < a - c" using tail_below_population by simp
  have K_at_least_four: "4 \<le> ?K" by (rule curriculum_scale_at_least_four)
  have K_le_gap_power: "?K \<le> ?K ^ (a - c)"
  proof -
    have decomposition: "a - c = 1 + (a - c - 1)"
      using gap_positive by simp
    have extra_at_least_one: "1 \<le> ?K ^ (a - c - 1)"
      by (rule one_le_power) (use K_at_least_four in simp)
    have "?K \<le> ?K * ?K ^ (a - c - 1)"
      using extra_at_least_one by simp
    also have "\<dots> = ?K ^ (a - c)"
      using decomposition by (simp add: power_add)
    finally show ?thesis .
  qed
  have twice_below_gap: "2 < ?K ^ (a - c)"
    using K_at_least_four K_le_gap_power by linarith
  have tail_positive: "0 < power_tail c k" by (rule power_tail_positive)
  have twice_tail_below_population:
    "2 * power_tail c k < power_population a k"
    using mult_strict_right_mono[OF twice_below_gap, of "power_tail c k"]
      power_population_factorization[OF tail_below_population, of k]
      tail_positive
    by (simp add: mult.commute)
  have counts: "power_tail c k + power_anchor a c k = power_population a k"
    by (rule power_counts[OF tail_below_population])
  show ?thesis using twice_tail_below_population counts by linarith
qed

text \<open>power_learning_rate_at_most_one: 対象量の上界を示す。\<close>
lemma power_learning_rate_at_most_one:
  "power_learning_rate b k \<le> 1"
proof -
  have denominator_at_least_one:
    "1 \<le> real (curriculum_scale k) ^ b"
    using curriculum_scale_at_least_four[of k] by simp
  have "1 / real (curriculum_scale k) ^ b \<le> (1::real) / 1"
    by (rule frac_le) (use denominator_at_least_one in simp_all)
  then show ?thesis unfolding power_learning_rate_def by simp
qed

text \<open>power_effective_tail_mass_exact: 対象量の厳密な閉形式を示す。\<close>
lemma power_effective_tail_mass_exact:
  assumes rate_below_tail: "b < c"
  shows "power_learning_rate b k * real (power_tail c k) =
    real (curriculum_scale k) ^ (c - b)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_nonzero: "?K \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have exponent: "b + (c - b) = c" using rate_below_tail by simp
  have power_factor: "?K ^ c = ?K ^ b * ?K ^ (c - b)"
  proof -
    have "?K ^ c = ?K ^ (b + (c - b))" using exponent by simp
    also have "\<dots> = ?K ^ b * ?K ^ (c - b)" by (rule power_add)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding power_learning_rate_def power_tail_def of_nat_power
    using K_nonzero power_factor by (simp add: field_simps)
qed

text \<open>power_effective_tail_mass_at_least_scale: 対象量の下界を示す。\<close>
lemma power_effective_tail_mass_at_least_scale:
  assumes rate_below_tail: "b < c"
  shows "real (curriculum_scale k) \<le>
    power_learning_rate b k * real (power_tail c k)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_at_least_one: "1 \<le> ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have exponent_positive: "0 < c - b" using rate_below_tail by simp
  have decomposition: "c - b = 1 + (c - b - 1)"
    using exponent_positive by simp
  have extra_at_least_one: "1 \<le> ?K ^ (c - b - 1)"
    by (rule one_le_power[OF K_at_least_one])
  have "?K \<le> ?K * ?K ^ (c - b - 1)"
    using extra_at_least_one K_at_least_one by (simp add: mult_left_mono)
  also have "\<dots> = ?K ^ (c - b)"
    using decomposition by (simp add: power_add)
  finally show ?thesis
    using power_effective_tail_mass_exact[OF rate_below_tail, of k] by simp
qed

text \<open>power_anchor_log_upper: 対数またはロジット比をスケール量に結び付ける。\<close>
lemma power_anchor_log_upper:
  assumes tail_below_population: "c < a"
  shows "ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k) - 1)) \<le>
    1 + real a * ln (real (curriculum_scale k))"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?N = "power_population a k"
  let ?n = "power_anchor a c k"
  let ?eta = "power_learning_rate b k"
  have K_positive: "0 < ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have N_positive: "0 < ?N" by (rule power_population_positive)
  have eta_positive: "0 < ?eta" by (rule power_learning_rate_positive)
  have eta_at_most_one: "?eta \<le> 1" by (rule power_learning_rate_at_most_one)
  have exp_difference_nonnegative: "0 \<le> exp ?eta - 1"
    using eta_positive by simp
  have exp_difference_upper: "exp ?eta - 1 \<le> exp 1 - 1"
    using eta_at_most_one by simp
  have n_le_N: "?n \<le> ?N"
    using power_counts[OF tail_below_population, of k] by linarith
  have scaled_upper:
    "real ?n * (exp ?eta - 1) \<le> real ?N * (exp 1 - 1)"
  proof -
    have "real ?n * (exp ?eta - 1) \<le> real ?N * (exp ?eta - 1)"
      by (rule mult_right_mono) (use n_le_N exp_difference_nonnegative in simp_all)
    also have "\<dots> \<le> real ?N * (exp 1 - 1)"
      by (rule mult_left_mono[OF exp_difference_upper]) simp
    finally show ?thesis .
  qed
  have argument_upper:
    "1 + real ?n * (exp ?eta - 1) \<le> exp 1 * real ?N"
  proof -
    have "1 + real ?n * (exp ?eta - 1) \<le>
        1 + real ?N * (exp 1 - 1)" using scaled_upper by linarith
    also have "\<dots> \<le> exp 1 * real ?N"
    proof -
      have N_at_least_one: "1 \<le> real ?N" using N_positive by simp
      have identity: "exp 1 * real ?N -
          (1 + real ?N * (exp 1 - 1)) = real ?N - 1" by algebra
      show ?thesis using N_at_least_one identity by linarith
    qed
    finally show ?thesis .
  qed
  have product_nonnegative: "0 \<le> real ?n * (exp ?eta - 1)"
    by (rule mult_nonneg_nonneg) (use exp_difference_nonnegative in simp_all)
  have argument_positive: "0 < 1 + real ?n * (exp ?eta - 1)"
    using product_nonnegative by linarith
  have logarithm_upper:
    "ln (1 + real ?n * (exp ?eta - 1)) \<le> ln (exp 1 * real ?N)"
    by (rule ln_mono[OF argument_upper argument_positive])
  have N_cast: "real ?N = ?K ^ a"
    unfolding power_population_def by simp
  have logarithm_identity: "ln (exp 1 * real ?N) = 1 + real a * ln ?K"
    unfolding N_cast using K_positive by (simp add: ln_mult ln_realpow)
  show ?thesis using logarithm_upper logarithm_identity by simp
qed

text \<open>power_anchor_log_over_scale_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_anchor_log_over_scale_tendsto_zero:
  assumes tail_below_population: "c < a"
  shows "((\<lambda>k. ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k) - 1)) /
      real (curriculum_scale k)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?A = "\<lambda>k. ln (1 + real (power_anchor a c k) *
    (exp (power_learning_rate b k) - 1))"
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using inverse_curriculum_power_tendsto_zero[of 1] by simp
  have scaled_log_limit:
    "((\<lambda>k. real a * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const curriculum_log_scale_over_scale_tendsto_zero,
        of "real a"] by simp
  have upper_limit:
    "((\<lambda>k. (1 + real a * ln (?K k)) / ?K k) \<longlongrightarrow> 0) sequentially"
  proof -
    have sum_limit:
      "((\<lambda>k. 1 / ?K k + real a * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_add[OF inverse_limit scaled_log_limit] by simp
    have identity: "(1 + real a * ln (?K k)) / ?K k =
      1 / ?K k + real a * (ln (?K k) / ?K k)" for k
      unfolding field_class.field_divide_inverse by algebra
    show ?thesis using sum_limit by (simp add: identity)
  qed
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 0 \<le> ?A k / ?K k"
  proof (intro always_eventually allI)
    fix k
    have eta_positive: "0 < power_learning_rate b k"
      by (rule power_learning_rate_positive)
    have exp_difference_nonnegative:
      "0 \<le> exp (power_learning_rate b k) - 1" using eta_positive by simp
    have product_nonnegative:
      "0 \<le> real (power_anchor a c k) *
        (exp (power_learning_rate b k) - 1)"
      by (rule mult_nonneg_nonneg) (use exp_difference_nonnegative in simp_all)
    have logarithm_nonnegative: "0 \<le> ?A k"
      using product_nonnegative by simp
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    show "0 \<le> ?A k / ?K k"
      by (rule divide_nonneg_nonneg) (use logarithm_nonnegative in simp_all)
  qed
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k \<le> (1 + real a * ln (?K k)) / ?K k"
  proof (intro always_eventually allI)
    fix k
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    show "?A k / ?K k \<le> (1 + real a * ln (?K k)) / ?K k"
      by (rule divide_right_mono[OF power_anchor_log_upper[OF tail_below_population]])
        (use K_positive in linarith)
  qed
  show ?thesis
    by (rule tendsto_sandwich[OF lower_bound upper_bound tendsto_const upper_limit])
qed

text \<open>power_tail_takeover_eventually: 十分大きな段階で成立する評価を示す。\<close>
lemma power_tail_takeover_eventually:
  assumes rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "\<forall>\<^sub>F k in sequentially.
    ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k) - 1)) + 1 <
    power_learning_rate b k * real (power_tail c k) / (1 + exp 1)"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?A = "\<lambda>k. ln (1 + real (power_anchor a c k) *
    (exp (power_learning_rate b k) - 1))"
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using inverse_curriculum_power_tendsto_zero[of 1] by simp
  have normalized_limit:
    "((\<lambda>k. ?A k / ?K k + 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF power_anchor_log_over_scale_tendsto_zero
      [OF tail_below_population, of b] inverse_limit] by simp
  have denominator_positive: "0 < 1 + exp (1::real)"
    using exp_gt_zero[of "1::real"] by linarith
  have target_positive: "0 < (1::real) / (1 + exp 1)"
    by (rule divide_pos_pos) (use denominator_positive in simp_all)
  have eventual_normalized: "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k + 1 / ?K k < 1 / (1 + exp 1)"
    using order_tendstoD(2)[OF normalized_limit, of "1 / (1 + exp 1)"]
      target_positive by simp
  show ?thesis
  proof (rule eventually_mono[OF eventual_normalized])
    fix k
    assume normalized:
      "?A k / ?K k + 1 / ?K k < 1 / (1 + exp 1)"
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have normalized_identity:
      "?A k / ?K k + 1 / ?K k = (?A k + 1) / ?K k"
      unfolding field_class.field_divide_inverse by algebra
    have first: "?A k + 1 < (1 / (1 + exp 1)) * ?K k"
      using normalized normalized_identity K_positive by (simp add: pos_divide_less_eq)
    have mass_lower: "?K k \<le>
        power_learning_rate b k * real (power_tail c k)"
      by (rule power_effective_tail_mass_at_least_scale[OF rate_below_tail])
    have coefficient_positive: "0 < (1::real) / (1 + exp 1)"
      using target_positive .
    have second: "(1 / (1 + exp 1)) * ?K k \<le>
        power_learning_rate b k * real (power_tail c k) / (1 + exp 1)"
      using mult_left_mono[OF mass_lower, of "1 / (1 + exp 1)"]
        coefficient_positive
      by (simp add: field_class.field_divide_inverse mult.commute)
    show "?A k + 1 <
      power_learning_rate b k * real (power_tail c k) / (1 + exp 1)"
      using first second by linarith
  qed
qed

text \<open>power_attack_margin_eventually: 十分大きな段階で成立する評価を示す。\<close>
lemma power_attack_margin_eventually:
  assumes rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "\<forall>\<^sub>F k in sequentially.
    attack_state (power_learning_rate b k)
      (power_anchor a c k) (power_tail c k) < -1"
proof (rule eventually_mono[OF power_tail_takeover_eventually
    [OF rate_below_tail tail_below_population]])
  fix k
  assume takeover:
    "ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k) - 1)) + 1 <
      power_learning_rate b k * real (power_tail c k) / (1 + exp 1)"
  have eta_positive: "0 < power_learning_rate b k"
    by (rule power_learning_rate_positive)
  have anchor_bound:
    "anchor_state (power_learning_rate b k) (power_anchor a c k) \<le>
      ln (1 + real (power_anchor a c k) *
        (exp (power_learning_rate b k) - 1))"
    by (rule anchor_log_bound) (use eta_positive in linarith)
  have product_identity:
    "real (power_tail c k) *
      (power_learning_rate b k * (1 / (1 + exp 1))) =
      power_learning_rate b k * real (power_tail c k) / (1 + exp 1)"
    unfolding field_class.field_divide_inverse by algebra
  have takeover_form:
    "ln (1 + real (power_anchor a c k) *
      (exp (power_learning_rate b k) - 1)) -
      real (power_tail c k) *
        (power_learning_rate b k * (1 / (1 + exp 1))) < -1"
    using takeover product_identity by linarith
  show "attack_state (power_learning_rate b k)
      (power_anchor a c k) (power_tail c k) < -1"
    by (rule logarithmic_anchor_bound_implies_inversion
      [OF eta_positive anchor_bound takeover_form])
qed

text \<open>logistic_contraction_power_le_exp: 対数またはロジット比をスケール量に結び付ける。\<close>
lemma logistic_contraction_power_le_exp:
  fixes eta :: real
  assumes N_positive: "0 < N"
    and counts: "m + n = N"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_one: "eta \<le> 1"
  shows "(1 - eta * (real m / real N) * (real n / real N)) ^ N \<le>
    exp (-(real N * eta * (real m / real N) * (real n / real N)))"
proof -
  let ?p = "real m / real N"
  let ?q = "real n / real N"
  let ?x = "eta * ?p * ?q"
  have N_real_positive: "0 < real N" using N_positive by simp
  have m_le_N: "m \<le> N" and n_le_N: "n \<le> N" using counts by linarith+
  have p_nonnegative: "0 \<le> ?p" and q_nonnegative: "0 \<le> ?q"
    by (intro divide_nonneg_nonneg; simp)+
  have real_m_le_N: "real m \<le> real N" using m_le_N by simp
  have real_n_le_N: "real n \<le> real N" using n_le_N by simp
  have p_at_most_one: "?p \<le> 1"
    using real_m_le_N N_real_positive by (simp only: divide_le_eq_1_pos)
  have q_at_most_one: "?q \<le> 1"
    using real_n_le_N N_real_positive by (simp only: divide_le_eq_1_pos)
  have eta_p_nonnegative: "0 \<le> eta * ?p"
    by (rule mult_nonneg_nonneg[OF eta_nonnegative p_nonnegative])
  have eta_p_at_most_one: "eta * ?p \<le> 1"
  proof -
    have "eta * ?p \<le> 1 * ?p"
      by (rule mult_right_mono[OF eta_at_most_one p_nonnegative])
    also have "\<dots> \<le> 1" using p_at_most_one by simp
    finally show ?thesis .
  qed
  have x_nonnegative: "0 \<le> ?x"
    by (rule mult_nonneg_nonneg[OF eta_p_nonnegative q_nonnegative])
  have x_at_most_one: "?x \<le> 1"
  proof -
    have "eta * ?p * ?q \<le> 1 * ?q"
      by (rule mult_right_mono[OF eta_p_at_most_one q_nonnegative])
    also have "\<dots> \<le> 1" using q_at_most_one by simp
    finally show ?thesis .
  qed
  have one_minus_nonnegative: "0 \<le> 1 - ?x" using x_at_most_one by linarith
  have step_bound: "1 - ?x \<le> exp (-?x)" by (rule exp_minus_ge)
  have power_bound: "(1 - ?x)^N \<le> (exp (-?x))^N"
    by (rule power_mono[OF step_bound one_minus_nonnegative])
  have exponential_identity: "(exp (-?x))^N = exp (-(real N * ?x))"
  proof -
    have "(exp (-?x))^N = exp (real N * (-?x))"
      by (rule exp_of_nat_mult[symmetric])
    also have "\<dots> = exp (-(real N * ?x))" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  from power_bound have "(1 - ?x)^N \<le> (exp (-?x))^N" .
  also have "\<dots> = exp (-(real N * ?x))" by (rule exponential_identity)
  finally show ?thesis by (simp only: mult.assoc)
qed

text \<open>power_contraction_mass_at_least_half_scale: 対象量の下界を示す。\<close>
lemma power_contraction_mass_at_least_half_scale:
  assumes rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "real (curriculum_scale k) / 2 \<le>
    real (power_population a k) * power_learning_rate b k *
      (real (power_tail c k) / real (power_population a k)) *
      (real (power_anchor a c k) / real (power_population a k))"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?N = "power_population a k"
  let ?m = "power_tail c k"
  let ?n = "power_anchor a c k"
  let ?eta = "power_learning_rate b k"
  let ?q = "real ?n / real ?N"
  have N_positive: "0 < ?N" by (rule power_population_positive)
  have N_real_positive: "0 < real ?N" using N_positive by simp
  have counts: "?m + ?n = ?N" by (rule power_counts[OF tail_below_population])
  have minority_smaller: "?m < ?n"
    by (rule power_tail_less_anchor[OF tail_below_population])
  have q_half: "1 / 2 < ?q"
  proof -
    have "real ?N < 2 * real ?n" using counts minority_smaller by simp
    then show ?thesis using N_real_positive
      by (simp add: pos_less_divide_eq; linarith)
  qed
  have q_nonnegative: "0 \<le> ?q" by simp
  have mass_lower: "?K \<le> ?eta * real ?m"
    by (rule power_effective_tail_mass_at_least_scale[OF rate_below_tail])
  have product_lower: "?K * (1 / 2) \<le> (?eta * real ?m) * ?q"
    by (rule mult_mono) (use mass_lower q_half q_nonnegative in simp_all)
  have mass_identity:
    "real ?N * ?eta * (real ?m / real ?N) * ?q =
      (?eta * real ?m) * ?q"
    using N_real_positive by (simp add: field_simps; algebra)
  have simple_bound: "?K / 2 \<le> (?eta * real ?m) * ?q"
    using product_lower by (simp only: field_class.field_divide_inverse)
  show ?thesis
  proof -
    have "?K / 2 \<le> (?eta * real ?m) * ?q" by (rule simple_bound)
    also have "\<dots> = real ?N * ?eta * (real ?m / real ?N) * ?q"
      by (rule mass_identity[symmetric])
    finally show ?thesis .
  qed
qed

text \<open>power_exp_half_scale_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_exp_half_scale_tendsto_zero:
  "((\<lambda>k. exp (-(real (curriculum_scale k) / 2))) \<longlongrightarrow> 0) sequentially"
proof -
  have scaled: "filterlim (\<lambda>k. (1 / 2::real) * real (curriculum_scale k))
      at_top sequentially"
    by (rule filterlim_tendsto_pos_mult_at_top[OF tendsto_const _
      curriculum_scale_filterlim]) simp
  have negative: "filterlim (\<lambda>k. -(real (curriculum_scale k) / 2))
      at_bot sequentially"
    unfolding filterlim_uminus_at_bot
  proof -
    have function_identity: "(\<lambda>k. - (-(real (curriculum_scale k) / 2))) =
        (\<lambda>k. (1 / 2::real) * real (curriculum_scale k))"
      by (rule ext) algebra
    show "filterlim (\<lambda>k. - (-(real (curriculum_scale k) / 2)))
        at_top sequentially"
      unfolding function_identity by (rule scaled)
  qed
  show ?thesis by (rule filterlim_compose[OF exp_at_bot negative])
qed

text \<open>power_contraction_factor_eventually_half: 十分大きな段階で成立する評価を示す。\<close>
lemma power_contraction_factor_eventually_half:
  assumes rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "\<forall>\<^sub>F k in sequentially. 1 / 2 \<le> 1 -
    (1 - power_learning_rate b k *
      (real (power_tail c k) / real (power_population a k)) *
      (real (power_anchor a c k) / real (power_population a k))) ^
      power_population a k"
proof -
  have exp_small: "\<forall>\<^sub>F k in sequentially.
      exp (-(real (curriculum_scale k) / 2)) < 1 / 2"
    using order_tendstoD(2)[OF power_exp_half_scale_tendsto_zero, of "1 / 2"]
    by simp
  show ?thesis
  proof (rule eventually_mono[OF exp_small])
    fix k
    assume upper: "exp (-(real (curriculum_scale k) / 2)) < 1 / 2"
    let ?N = "power_population a k"
    let ?m = "power_tail c k"
    let ?n = "power_anchor a c k"
    let ?eta = "power_learning_rate b k"
    let ?mass = "real ?N * ?eta * (real ?m / real ?N) *
      (real ?n / real ?N)"
    have mass_lower: "real (curriculum_scale k) / 2 \<le> ?mass"
      by (rule power_contraction_mass_at_least_half_scale
        [OF rate_below_tail tail_below_population])
    have exp_mass_upper: "exp (-?mass) \<le>
        exp (-(real (curriculum_scale k) / 2))"
      using mass_lower by simp
    have contraction_upper: "(1 - ?eta * (real ?m / real ?N) *
        (real ?n / real ?N)) ^ ?N \<le> exp (-?mass)"
      by (rule logistic_contraction_power_le_exp)
        (use power_population_positive[of a k]
          power_counts[OF tail_below_population, of k]
          power_learning_rate_positive[of b k]
          power_learning_rate_at_most_one[of b k] in linarith)+
    have "(1 - ?eta * (real ?m / real ?N) * (real ?n / real ?N)) ^ ?N < 1 / 2"
      using contraction_upper exp_mass_upper upper by linarith
    then show "1 / 2 \<le> 1 -
      (1 - ?eta * (real ?m / real ?N) * (real ?n / real ?N)) ^ ?N"
      by linarith
  qed
qed

text \<open>power_anchor_tail_ratio_exact: アンカーとテールの比率に関する恒等式または境界を示す。\<close>
lemma power_anchor_tail_ratio_exact:
  assumes tail_below_population: "c < a"
  shows "real (power_anchor a c k) / real (power_tail c k) =
    real (curriculum_scale k) ^ (a - c) - 1"
proof -
  let ?K = "real (curriculum_scale k)"
  let ?N = "power_population a k"
  let ?m = "power_tail c k"
  let ?n = "power_anchor a c k"
  have m_positive: "0 < ?m" by (rule power_tail_positive)
  have m_real_nonzero: "real ?m \<noteq> 0" using m_positive by simp
  have m_le_N: "?m \<le> ?N" by (rule power_tail_le_population[OF tail_below_population])
  have cast_anchor: "real ?n = real ?N - real ?m"
    unfolding power_anchor_def using m_le_N by simp
  have cast_factorization: "real ?N = real ?m * ?K ^ (a - c)"
    using power_population_factorization[OF tail_below_population, of k] by simp
  show ?thesis using cast_anchor cast_factorization m_real_nonzero
    by (simp add: field_simps; algebra)
qed

text \<open>power_log_odds_exact: 対数またはロジット比をスケール量に結び付ける。\<close>
lemma power_log_odds_exact:
  assumes tail_below_population: "c < a"
  shows "ln ((real (power_anchor a c k) / real (power_population a k)) /
      (real (power_tail c k) / real (power_population a k))) =
    ln (real (curriculum_scale k) ^ (a - c) - 1)"
proof -
  have N_positive: "0 < real (power_population a k)"
    using power_population_positive[of a k] by simp
  have m_positive: "0 < real (power_tail c k)"
    using power_tail_positive[of c k] by simp
  have ratio_identity:
    "(real (power_anchor a c k) / real (power_population a k)) /
      (real (power_tail c k) / real (power_population a k)) =
      real (power_anchor a c k) / real (power_tail c k)"
    using N_positive m_positive by (simp add: field_simps)
  show ?thesis
    using ratio_identity power_anchor_tail_ratio_exact[OF tail_below_population, of k]
    by simp
qed

text \<open>power_log_odds_filterlim: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_log_odds_filterlim:
  assumes tail_below_population: "c < a"
  shows "filterlim (\<lambda>k. ln (real (curriculum_scale k) ^ (a - c) - 1))
    at_top sequentially"
proof -
  have gap_positive: "0 < a - c" using tail_below_population by simp
  show ?thesis unfolding filterlim_at_top
  proof
    fix z :: real
    have base_eventually: "\<forall>\<^sub>F k in sequentially.
        z \<le> ln (real (curriculum_scale k) - 1)"
      using curriculum_log_odds_filterlim unfolding filterlim_at_top by blast
    show "\<forall>\<^sub>F k in sequentially.
      z \<le> ln (real (curriculum_scale k) ^ (a - c) - 1)"
    proof (rule eventually_mono[OF base_eventually])
      fix k
      assume lower: "z \<le> ln (real (curriculum_scale k) - 1)"
      let ?K = "real (curriculum_scale k)"
      have K_at_least_four: "4 \<le> ?K"
        using curriculum_scale_at_least_four[of k] by simp
      have K_at_least_one: "1 \<le> ?K" using K_at_least_four by linarith
      have decomposition: "a - c = 1 + (a - c - 1)"
        using gap_positive by simp
      have extra_at_least_one: "1 \<le> ?K ^ (a - c - 1)"
        by (rule one_le_power[OF K_at_least_one])
      have K_le_power: "?K \<le> ?K ^ (a - c)"
      proof -
        have "?K \<le> ?K * ?K ^ (a - c - 1)"
          using extra_at_least_one K_at_least_one by simp
        also have "\<dots> = ?K ^ (a - c)"
          using decomposition by (simp add: power_add)
        finally show ?thesis .
      qed
      have argument_positive: "0 < ?K - 1" using K_at_least_four by linarith
      have log_mono: "ln (?K - 1) \<le> ln (?K ^ (a - c) - 1)"
        by (rule ln_mono) (use K_le_power argument_positive in linarith)+
      show "z \<le> ln (?K ^ (a - c) - 1)" using lower log_mono by linarith
    qed
  qed
qed

text \<open>power_random_error: 冪スケーリングのランダム順序誤差を定める。\<close>
definition power_random_error :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "power_random_error a b k = power_learning_rate b k *
    sqrt (real (power_population a k) / 2 *
      ln (2 * real (power_population a k) / power_confidence k))"

text \<open>power_random_log_argument: 対数またはロジット比をスケール量に結び付ける。\<close>
lemma power_random_log_argument:
  "2 * real (power_population a k) / power_confidence k =
    2 * real (curriculum_scale k) ^ (a + 2)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_nonzero: "?K \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have power_sum: "?K ^ (a + 2) = ?K ^ a * ?K ^ 2" by (rule power_add)
  show ?thesis
    unfolding power_population_def power_confidence_def of_nat_power
    using K_nonzero power_sum by (simp add: field_simps)
qed

text \<open>power_random_log_nonnegative: 対数またはロジット比をスケール量に結び付ける。\<close>
lemma power_random_log_nonnegative:
  "0 \<le> ln (2 * real (power_population a k) / power_confidence k)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_at_least_one: "1 \<le> ?K"
    using curriculum_scale_at_least_four[of k] by simp
  have power_at_least_one: "1 \<le> ?K ^ (a + 2)"
    by (rule one_le_power[OF K_at_least_one])
  have "0 \<le> ln (2 * ?K ^ (a + 2))" using power_at_least_one by simp
  then show ?thesis using power_random_log_argument[of a k] by simp
qed

text \<open>power_random_error_nonnegative: 誤差または状態の明示的な上界を与える。\<close>
lemma power_random_error_nonnegative:
  "0 \<le> power_random_error a b k"
proof -
  have inside_nonnegative: "0 \<le> real (power_population a k) / 2 *
      ln (2 * real (power_population a k) / power_confidence k)"
    by (rule mult_nonneg_nonneg) (use power_random_log_nonnegative[of a k] in simp_all)
  have root_nonnegative: "0 \<le> sqrt (real (power_population a k) / 2 *
      ln (2 * real (power_population a k) / power_confidence k))"
    by (rule real_sqrt_ge_zero[OF inside_nonnegative])
  show ?thesis unfolding power_random_error_def
    by (rule mult_nonneg_nonneg[OF _ root_nonnegative])
      (use power_learning_rate_positive[of b k] in linarith)
qed

text \<open>power_noise_mass_exact: 対象量の厳密な閉形式を示す。\<close>
lemma power_noise_mass_exact:
  assumes noise_condition: "a < 2 * b"
  shows "power_learning_rate b k ^ 2 * real (power_population a k) =
    1 / real (curriculum_scale k) ^ (2 * b - a)"
proof -
  let ?K = "real (curriculum_scale k)"
  have K_nonzero: "?K \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  have exponent: "a + (2 * b - a) = 2 * b" using noise_condition by simp
  have denominator_factor: "?K ^ (2 * b) = ?K ^ a * ?K ^ (2 * b - a)"
  proof -
    have "?K ^ (2 * b) = ?K ^ (a + (2 * b - a))" using exponent by simp
    also have "\<dots> = ?K ^ a * ?K ^ (2 * b - a)" by (rule power_add)
    finally show ?thesis .
  qed
  have square_power: "(?K ^ b)^2 = ?K ^ (2 * b)"
  proof -
    have "(?K ^ b)^2 = ?K ^ (b * 2)" by (rule power_mult[symmetric])
    also have "\<dots> = ?K ^ (2 * b)" by (simp add: mult.commute)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding power_learning_rate_def power_population_def of_nat_power
    using K_nonzero denominator_factor square_power by (simp add: field_simps)
qed

text \<open>power_random_error_square: 誤差または状態の明示的な上界を与える。\<close>
lemma power_random_error_square:
  assumes noise_condition: "a < 2 * b"
  shows "power_random_error a b k ^ 2 =
    ln (2 * real (curriculum_scale k) ^ (a + 2)) /
      (2 * real (curriculum_scale k) ^ (2 * b - a))"
proof -
  let ?L = "ln (2 * real (power_population a k) / power_confidence k)"
  let ?X = "real (power_population a k) / 2 * ?L"
  have X_nonnegative: "0 \<le> ?X"
    by (rule mult_nonneg_nonneg) (use power_random_log_nonnegative[of a k] in simp_all)
  have square_expansion: "power_random_error a b k ^ 2 =
      power_learning_rate b k ^ 2 * ?X"
    unfolding power_random_error_def
    using X_nonnegative by (simp add: power_mult_distrib)
  have mass_exact: "power_learning_rate b k ^ 2 *
      real (power_population a k) =
      1 / real (curriculum_scale k) ^ (2 * b - a)"
    by (rule power_noise_mass_exact[OF noise_condition])
  have logarithm_exact: "?L = ln (2 * real (curriculum_scale k) ^ (a + 2))"
    using power_random_log_argument[of a k] by simp
  have regrouped: "power_random_error a b k ^ 2 =
      (power_learning_rate b k ^ 2 * real (power_population a k)) * ?L / 2"
    using square_expansion by algebra
  have substituted: "power_random_error a b k ^ 2 =
      (1 / real (curriculum_scale k) ^ (2 * b - a)) * ?L / 2"
    using regrouped mass_exact by simp
  have denominator_nonzero: "real (curriculum_scale k) ^ (2 * b - a) \<noteq> 0"
    using curriculum_scale_at_least_four[of k] by simp
  show ?thesis
    using substituted logarithm_exact denominator_nonzero
    by (simp add: field_simps; algebra)
qed

text \<open>power_random_error_square_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_random_error_square_tendsto_zero:
  assumes noise_condition: "a < 2 * b"
  shows "((\<lambda>k. power_random_error a b k ^ 2) \<longlongrightarrow> 0) sequentially"
proof -
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?d = "2 * b - a"
  let ?L = "\<lambda>k. ln (2 * ?K k ^ (a + 2))"
  have d_positive: "0 < ?d" using noise_condition by simp
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using inverse_curriculum_power_tendsto_zero[of 1] by simp
  have constant_limit: "((\<lambda>k. (ln 2 / 2) * (1 / ?K k)) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const inverse_limit, of "ln 2 / 2"] by simp
  have log_limit: "((\<lambda>k. (real (a + 2) / 2) *
      (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const curriculum_log_scale_over_scale_tendsto_zero,
      of "real (a + 2) / 2"] by simp
  have upper_limit: "((\<lambda>k. ?L k / (2 * ?K k)) \<longlongrightarrow> 0) sequentially"
  proof -
    have sum_limit: "((\<lambda>k. (ln 2 / 2) * (1 / ?K k) +
      (real (a + 2) / 2) * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_add[OF constant_limit log_limit] by simp
    have identity: "?L k / (2 * ?K k) =
      (ln 2 / 2) * (1 / ?K k) +
      (real (a + 2) / 2) * (ln (?K k) / ?K k)" for k
    proof -
      have K_positive: "0 < ?K k"
        using curriculum_scale_at_least_four[of k] by simp
      have logarithm_identity: "?L k = ln 2 + real (a + 2) * ln (?K k)"
      proof -
        have "?L k = ln 2 + ln (?K k ^ (a + 2))"
          using K_positive by (simp add: ln_mult)
        also have "\<dots> = ln 2 + real (a + 2) * ln (?K k)"
          by (simp only: ln_realpow)
        finally show ?thesis .
      qed
      have inverse_product: "inverse (2 * ?K k) =
          inverse 2 * inverse (?K k)" by simp
      show ?thesis
        unfolding field_class.field_divide_inverse
        using logarithm_identity inverse_product by algebra
    qed
    have function_identity:
      "(\<lambda>k. ?L k / (2 * ?K k)) = (\<lambda>k.
        (ln 2 / 2) * (1 / ?K k) +
        (real (a + 2) / 2) * (ln (?K k) / ?K k))"
      by (rule ext) (rule identity)
    show ?thesis unfolding function_identity by (rule sum_limit)
  qed
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 0 \<le> power_random_error a b k ^ 2"
    by (intro always_eventually allI) simp
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      power_random_error a b k ^ 2 \<le> ?L k / (2 * ?K k)"
  proof (intro always_eventually allI)
    fix k
    have K_at_least_one: "1 \<le> ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have decomposition: "?d = 1 + (?d - 1)" using d_positive by simp
    have extra_at_least_one: "1 \<le> ?K k ^ (?d - 1)"
      by (rule one_le_power[OF K_at_least_one])
    have K_le_power: "?K k \<le> ?K k ^ ?d"
    proof -
      have "?K k \<le> ?K k * ?K k ^ (?d - 1)"
        using extra_at_least_one K_at_least_one by simp
      also have "\<dots> = ?K k ^ ?d" using decomposition by (simp add: power_add)
      finally show ?thesis .
    qed
    have L_nonnegative: "0 \<le> ?L k"
      using power_random_log_nonnegative[of a k]
        power_random_log_argument[of a k] by simp
    have denominator_positive: "0 < 2 * ?K k" using K_at_least_one by linarith
    have fraction_mono: "?L k / (2 * ?K k ^ ?d) \<le> ?L k / (2 * ?K k)"
      by (rule divide_left_mono) (use K_le_power L_nonnegative denominator_positive in simp_all)
    show "power_random_error a b k ^ 2 \<le> ?L k / (2 * ?K k)"
      using power_random_error_square[OF noise_condition, of k] fraction_mono by simp
  qed
  show ?thesis
    by (rule tendsto_sandwich[OF lower_bound upper_bound tendsto_const upper_limit])
qed

text \<open>power_random_error_tendsto_zero: 対応する量が段階極限で 0 へ収束することを示す。\<close>
lemma power_random_error_tendsto_zero:
  assumes noise_condition: "a < 2 * b"
  shows "((\<lambda>k. power_random_error a b k) \<longlongrightarrow> 0) sequentially"
proof -
  have square_limit: "((\<lambda>k. power_random_error a b k ^ 2) \<longlongrightarrow> 0) sequentially"
    by (rule power_random_error_square_tendsto_zero[OF noise_condition])
  have root_limit: "((\<lambda>k. sqrt (power_random_error a b k ^ 2)) \<longlongrightarrow> sqrt 0) sequentially"
    by (rule tendsto_real_sqrt[OF square_limit])
  have function_identity: "(\<lambda>k. sqrt (power_random_error a b k ^ 2)) =
      (\<lambda>k. power_random_error a b k)"
  proof (rule ext)
    fix k
    show "sqrt (power_random_error a b k ^ 2) = power_random_error a b k"
      using power_random_error_nonnegative[of a b k] by simp
  qed
  show ?thesis using root_limit function_identity by simp
qed

text \<open>power_random_margin_exact: 更新後の分類マージンを評価する。\<close>
lemma power_random_margin_exact:
  assumes tail_below_population: "c < a"
  shows "random_order_lower_margin
      (power_learning_rate b k) (power_anchor a c k)
      (power_tail c k) (power_population a k) (power_confidence k) =
    ln (real (curriculum_scale k) ^ (a - c) - 1) *
      (1 - (1 - power_learning_rate b k *
        (real (power_tail c k) / real (power_population a k)) *
        (real (power_anchor a c k) / real (power_population a k))) ^
        power_population a k) - power_random_error a b k"
  unfolding random_order_lower_margin_def power_random_error_def
  using power_log_odds_exact[OF tail_below_population, where k=k]
  by simp

text \<open>power_random_margin_eventually_gt_one: 更新後の分類マージンを評価する。\<close>
lemma power_random_margin_eventually_gt_one:
  assumes noise_condition: "a < 2 * b"
    and rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "\<forall>\<^sub>F k in sequentially.
    1 < random_order_lower_margin
      (power_learning_rate b k) (power_anchor a c k)
      (power_tail c k) (power_population a k) (power_confidence k)"
proof -
  have logarithm_large: "\<forall>\<^sub>F k in sequentially.
      4 \<le> ln (real (curriculum_scale k) ^ (a - c) - 1)"
    using power_log_odds_filterlim[OF tail_below_population]
    unfolding filterlim_at_top by simp
  have error_small: "\<forall>\<^sub>F k in sequentially. power_random_error a b k < 1"
    using order_tendstoD(2)[OF power_random_error_tendsto_zero[OF noise_condition],
      of "1"] by simp
  note combined = eventually_conj[OF logarithm_large
      eventually_conj[OF power_contraction_factor_eventually_half[OF
        rate_below_tail tail_below_population] error_small]]
  show ?thesis
  proof (rule eventually_mono[OF combined])
    fix k
    assume facts: "4 \<le> ln (real (curriculum_scale k) ^ (a - c) - 1) \<and>
      1 / 2 \<le> 1 -
        (1 - power_learning_rate b k *
          (real (power_tail c k) / real (power_population a k)) *
          (real (power_anchor a c k) / real (power_population a k))) ^
          power_population a k \<and>
      power_random_error a b k < 1"
    let ?L = "ln (real (curriculum_scale k) ^ (a - c) - 1)"
    let ?C = "1 -
      (1 - power_learning_rate b k *
        (real (power_tail c k) / real (power_population a k)) *
        (real (power_anchor a c k) / real (power_population a k))) ^
        power_population a k"
    have L_nonnegative: "0 \<le> ?L" using facts by linarith
    have C_nonnegative: "0 \<le> ?C" using facts by linarith
    have product_lower: "4 * (1 / 2) \<le> ?L * ?C"
      by (rule mult_mono) (use facts L_nonnegative C_nonnegative in linarith)+
    have margin_identity: "random_order_lower_margin
        (power_learning_rate b k) (power_anchor a c k)
        (power_tail c k) (power_population a k) (power_confidence k) =
      ?L * ?C - power_random_error a b k"
      by (rule power_random_margin_exact[OF tail_below_population])
    show "1 < random_order_lower_margin
      (power_learning_rate b k) (power_anchor a c k)
      (power_tail c k) (power_population a k) (power_confidence k)"
      using product_lower facts margin_identity by linarith
  qed
qed

text \<open>power_random_benign_event: 冪スケーリングで正常なランダム順序となる事象を定める。\<close>
definition power_random_benign_event :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list set" where
  "power_random_benign_event a b c k = {xs.
    clean_test_risk (power_tail_ratio a c k)
      (binary_logistic_state (power_learning_rate b k)
        (real (power_anchor a c k) / real (power_population a k)) xs
        (power_population a k)) = power_tail_ratio a c k \<and>
    clean_test_auc (power_tail_ratio a c k)
      (binary_logistic_state (power_learning_rate b k)
        (real (power_anchor a c k) / real (power_population a k)) xs
        (power_population a k)) = 1 - power_tail_ratio a c k}"

text \<open>power_law_inversion_eventually: 十分大きな段階で成立する評価を示す。\<close>
lemma power_law_inversion_eventually:
  assumes noise_condition: "a < 2 * b"
    and rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "\<forall>\<^sub>F k in sequentially.
    clean_test_risk (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k)) =
      1 - power_tail_ratio a c k \<and>
    clean_test_auc (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k)) =
      power_tail_ratio a c k \<and>
    1 - power_confidence k \<le>
      uniform_probability
        (binary_orders (power_anchor a c k) (power_population a k))
        (power_random_benign_event a b c k)"
proof -
  note asymptotic = eventually_conj[OF
    power_tail_takeover_eventually[OF rate_below_tail tail_below_population]
    power_random_margin_eventually_gt_one[OF noise_condition rate_below_tail
      tail_below_population]]
  show ?thesis
  proof (rule eventually_mono[OF asymptotic])
    fix k
    assume limits: "ln (1 + real (power_anchor a c k) *
        (exp (power_learning_rate b k) - 1)) + 1 <
      power_learning_rate b k * real (power_tail c k) / (1 + exp 1) \<and>
      1 < random_order_lower_margin (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k) (power_population a k)
        (power_confidence k)"
    let ?N = "power_population a k"
    let ?m = "power_tail c k"
    let ?n = "power_anchor a c k"
    let ?eta = "power_learning_rate b k"
    let ?delta = "power_confidence k"
    let ?epsilon = "power_tail_ratio a c k"
    have N_positive: "0 < ?N" by (rule power_population_positive)
    have counts: "?m + ?n = ?N"
      by (rule power_counts[OF tail_below_population])
    have m_positive: "0 < ?m" by (rule power_tail_positive)
    have m_less_n: "?m < ?n"
      by (rule power_tail_less_anchor[OF tail_below_population])
    have eta_positive: "0 < ?eta" by (rule power_learning_rate_positive)
    have eta_at_most_four: "?eta \<le> 4"
      using power_learning_rate_at_most_one[of b k] by linarith
    have delta_positive: "0 < ?delta" by (rule power_confidence_positive)
    have delta_at_most_one: "?delta \<le> 1"
      by (rule power_confidence_at_most_one)
    have epsilon_nonnegative: "0 \<le> ?epsilon"
      unfolding power_tail_ratio_def by simp
    have epsilon_below_half: "?epsilon < 1 / 2"
    proof -
      have N_less_twice_anchor: "real ?N < 2 * real ?n"
        using counts m_less_n by simp
      have twice_tail_less_N: "2 * real ?m < real ?N"
        using counts N_less_twice_anchor by simp
      show ?thesis unfolding power_tail_ratio_def
        using N_positive twice_tail_less_N
        by (simp add: pos_less_divide_eq; linarith)
    qed
    have random_margin_positive:
      "0 < random_order_lower_margin ?eta ?n ?m ?N ?delta"
      using limits by linarith
    note inversion = finite_pool_order_only_inversion[OF N_positive counts
      m_positive m_less_n eta_positive eta_at_most_four _ delta_positive
      delta_at_most_one epsilon_nonnegative epsilon_below_half _
      random_margin_positive, of "1"]
    have gamma_positive: "0 < (1::real)" by simp
    have attack_risk: "clean_test_risk ?epsilon (attack_state ?eta ?n ?m) =
        1 - ?epsilon"
      by (rule finite_pool_order_only_inversion(1)[OF N_positive counts
        m_positive m_less_n eta_positive eta_at_most_four gamma_positive
        delta_positive delta_at_most_one epsilon_nonnegative epsilon_below_half])
        (use limits random_margin_positive in linarith)+
    have attack_auc: "clean_test_auc ?epsilon (attack_state ?eta ?n ?m) =
        ?epsilon"
      by (rule finite_pool_order_only_inversion(2)[OF N_positive counts
        m_positive m_less_n eta_positive eta_at_most_four gamma_positive
        delta_positive delta_at_most_one epsilon_nonnegative epsilon_below_half])
        (use limits random_margin_positive in linarith)+
    have strong_probability: "1 - ?delta \<le> uniform_probability
      (binary_orders ?n ?N)
      {xs. clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = ?epsilon \<and>
        clean_test_auc ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = 1 - ?epsilon \<and>
        clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) <
          clean_test_risk ?epsilon (attack_state ?eta ?n ?m) \<and>
        clean_test_auc ?epsilon (attack_state ?eta ?n ?m) <
          clean_test_auc ?epsilon
            (binary_logistic_state ?eta (real ?n / real ?N) xs ?N)}"
      by (rule finite_pool_order_only_inversion(3)[OF N_positive counts
        m_positive m_less_n eta_positive eta_at_most_four gamma_positive
        delta_positive delta_at_most_one epsilon_nonnegative epsilon_below_half])
        (use limits random_margin_positive in linarith)+
    have event_subset: "{xs. clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = ?epsilon \<and>
        clean_test_auc ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = 1 - ?epsilon \<and>
        clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) <
          clean_test_risk ?epsilon (attack_state ?eta ?n ?m) \<and>
        clean_test_auc ?epsilon (attack_state ?eta ?n ?m) <
          clean_test_auc ?epsilon
            (binary_logistic_state ?eta (real ?n / real ?N) xs ?N)} \<subseteq>
        power_random_benign_event a b c k"
      unfolding power_random_benign_event_def by blast
    have probability_mono: "uniform_probability (binary_orders ?n ?N)
        {xs. clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = ?epsilon \<and>
        clean_test_auc ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) = 1 - ?epsilon \<and>
        clean_test_risk ?epsilon
          (binary_logistic_state ?eta (real ?n / real ?N) xs ?N) <
          clean_test_risk ?epsilon (attack_state ?eta ?n ?m) \<and>
        clean_test_auc ?epsilon (attack_state ?eta ?n ?m) <
          clean_test_auc ?epsilon
            (binary_logistic_state ?eta (real ?n / real ?N) xs ?N)} \<le>
      uniform_probability (binary_orders ?n ?N)
        (power_random_benign_event a b c k)"
      by (rule uniform_probability_mono[OF finite_binary_orders event_subset])
    show "clean_test_risk ?epsilon (attack_state ?eta ?n ?m) =
        1 - ?epsilon \<and>
      clean_test_auc ?epsilon (attack_state ?eta ?n ?m) = ?epsilon \<and>
      1 - ?delta \<le> uniform_probability (binary_orders ?n ?N)
        (power_random_benign_event a b c k)"
      using attack_risk attack_auc strong_probability probability_mono by linarith
  qed
qed

text \<open>power_random_benign_probability: 冪スケーリング族の対応する漸近性質を示す。\<close>
definition power_random_benign_probability :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "power_random_benign_probability a b c k = uniform_probability
    (binary_orders (power_anchor a c k) (power_population a k))
    (power_random_benign_event a b c k)"

text \<open>power_random_benign_probability_tendsto_one: 対応する量が段階極限で 1 へ収束することを示す。\<close>
lemma power_random_benign_probability_tendsto_one:
  assumes noise_condition: "a < 2 * b"
    and rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "((\<lambda>k. power_random_benign_probability a b c k) \<longlongrightarrow> 1) sequentially"
proof -
  have lower_limit: "((\<lambda>k. 1 - power_confidence k) \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const power_confidence_tendsto_zero] by simp
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 1 - power_confidence k \<le>
      power_random_benign_probability a b c k"
    using power_law_inversion_eventually[OF noise_condition rate_below_tail
      tail_below_population]
    unfolding power_random_benign_probability_def by eventually_elim simp
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      power_random_benign_probability a b c k \<le> 1"
    by (intro always_eventually allI)
      (simp add: power_random_benign_probability_def
        uniform_probability_le_one[OF finite_binary_orders])
  show ?thesis
    by (rule tendsto_sandwich[OF lower_bound upper_bound lower_limit tendsto_const])
qed

text \<open>power_attack_metric_limits: リスクと AUC の極限をまとめて示す。\<close>
lemma power_attack_metric_limits:
  assumes noise_condition: "a < 2 * b"
    and rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "((\<lambda>k.
    (clean_test_risk (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k)),
     clean_test_auc (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k)))) \<longlongrightarrow> (1, 0)) sequentially"
proof -
  have risk_reference: "((\<lambda>k. 1 - power_tail_ratio a c k) \<longlongrightarrow> 1) sequentially"
    using tendsto_diff[OF tendsto_const
      power_tail_ratio_tendsto_zero[OF tail_below_population]] by simp
  note inversion = power_law_inversion_eventually[OF noise_condition
    rate_below_tail tail_below_population]
  have risk_identity: "\<forall>\<^sub>F k in sequentially. 1 - power_tail_ratio a c k =
      clean_test_risk (power_tail_ratio a c k)
        (attack_state (power_learning_rate b k)
          (power_anchor a c k) (power_tail c k))"
    using inversion by eventually_elim simp
  have auc_identity: "\<forall>\<^sub>F k in sequentially. power_tail_ratio a c k =
      clean_test_auc (power_tail_ratio a c k)
        (attack_state (power_learning_rate b k)
          (power_anchor a c k) (power_tail c k))"
    using inversion by eventually_elim simp
  have risk_limit: "((\<lambda>k. clean_test_risk (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k))) \<longlongrightarrow> 1) sequentially"
    by (rule Lim_transform_eventually[OF risk_reference risk_identity])
  have auc_limit: "((\<lambda>k. clean_test_auc (power_tail_ratio a c k)
      (attack_state (power_learning_rate b k)
        (power_anchor a c k) (power_tail c k))) \<longlongrightarrow> 0) sequentially"
    by (rule Lim_transform_eventually[OF
      power_tail_ratio_tendsto_zero[OF tail_below_population] auc_identity])
  show ?thesis by (intro tendsto_Pair risk_limit auc_limit)
qed

text \<open>power_law_order_only_inversion: 攻撃順序と正常順序の間で学習挙動が反転することを示す。\<close>
theorem power_law_order_only_inversion:
  assumes noise_condition: "a < 2 * b"
    and rate_below_tail: "b < c"
    and tail_below_population: "c < a"
  shows "((\<lambda>k. power_tail_ratio a c k) \<longlongrightarrow> 0) sequentially"
    and "(power_confidence \<longlongrightarrow> 0) sequentially"
    and "((\<lambda>k. power_random_benign_probability a b c k) \<longlongrightarrow> 1) sequentially"
    and "((\<lambda>k.
      (clean_test_risk (power_tail_ratio a c k)
        (attack_state (power_learning_rate b k)
          (power_anchor a c k) (power_tail c k)),
       clean_test_auc (power_tail_ratio a c k)
        (attack_state (power_learning_rate b k)
          (power_anchor a c k) (power_tail c k)))) \<longlongrightarrow> (1, 0)) sequentially"
  by (rule power_tail_ratio_tendsto_zero[OF tail_below_population],
      rule power_confidence_tendsto_zero,
      rule power_random_benign_probability_tendsto_one[OF noise_condition
        rate_below_tail tail_below_population],
      rule power_attack_metric_limits[OF noise_condition rate_below_tail
        tail_below_population])

primrec normed_additive_iteration ::
    "('a::real_normed_vector \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "normed_additive_iteration F e x 0 = x"
| "normed_additive_iteration F e x (Suc k) =
    F (normed_additive_iteration F e x k) + e k"

text \<open>normed_additive_iteration_error_bound: アンカーとテールの比率に関する恒等式または境界を示す。\<close>
theorem normed_additive_iteration_error_bound:
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes nonexpansive: "\<And>u v. norm (F u - F v) \<le> norm (u - v)"
  shows "norm (normed_additive_iteration F e x N - (F ^^ N) x) \<le>
    (\<Sum>i<N. norm (e i))"
proof (induction N)
  case 0
  show ?case by simp
next
  case (Suc k)
  let ?actual = "normed_additive_iteration F e x k"
  let ?ideal = "(F ^^ k) x"
  have iterate_identity:
    "normed_additive_iteration F e x (Suc k) - (F ^^ Suc k) x =
      (F ?actual - F ?ideal) + e k"
    by (simp add: funpow_Suc_right algebra_simps)
  have triangle:
    "norm (normed_additive_iteration F e x (Suc k) - (F ^^ Suc k) x) \<le>
      norm (F ?actual - F ?ideal) + norm (e k)"
    unfolding iterate_identity by (rule norm_triangle_ineq)
  have dynamics_bound: "norm (F ?actual - F ?ideal) \<le> norm (?actual - ?ideal)"
    by (rule nonexpansive)
  have step_bound:
    "norm (normed_additive_iteration F e x (Suc k) - (F ^^ Suc k) x) \<le>
      norm (?actual - ?ideal) + norm (e k)"
    using triangle dynamics_bound by linarith
  show ?case using step_bound Suc.IH by simp
qed

text \<open>binary_logistic_prefix_discrepancy_control: 対数またはロジット比をスケール量に結び付ける。\<close>
theorem binary_logistic_prefix_discrepancy_control:
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and xs_order: "xs \<in> binary_orders n N"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and prefix_discrepancy: "\<And>j. j \<le> N \<Longrightarrow>
      abs (prefix_sum (binary_innovation (real n / real N) xs) j) \<le> D"
  shows "abs (binary_logistic_state eta (real n / real N) xs N -
      mean_logistic_state eta (real n / real N) N) \<le> eta * D"
    and "mean_logistic_state eta (real n / real N) N - eta * D \<le>
      binary_logistic_state eta (real n / real N) xs N"
proof -
  have displacement:
    "min e 0 \<le> mean_logistic_step eta (real n / real N) (y + e) -
        mean_logistic_step eta (real n / real N) y \<and>
      mean_logistic_step eta (real n / real N) (y + e) -
        mean_logistic_step eta (real n / real N) y \<le> max e 0"
    for y e
    by (rule mean_logistic_step_displacement[OF eta_nonnegative eta_at_most_four])
  have total_zero:
    "prefix_sum (binary_innovation (real n / real N) xs) N = 0"
    by (rule binary_innovation_total_zero[OF N_positive sample_size xs_order])
  have absolute_bound:
    "abs (binary_logistic_state eta (real n / real N) xs N -
      mean_logistic_state eta (real n / real N) N) \<le> eta * D"
    unfolding binary_logistic_state_def mean_logistic_state_def
    by (rule prefix_controlled_perturbation[OF eta_nonnegative displacement
          prefix_discrepancy total_zero])
  show "abs (binary_logistic_state eta (real n / real N) xs N -
      mean_logistic_state eta (real n / real N) N) \<le> eta * D"
    by (fact absolute_bound)
  show "mean_logistic_state eta (real n / real N) N - eta * D \<le>
      binary_logistic_state eta (real n / real N) xs N"
    using absolute_bound abs_ge_minus_self[of
      "binary_logistic_state eta (real n / real N) xs N -
       mean_logistic_state eta (real n / real N) N"]
    by linarith
qed

text \<open>binary_logistic_low_discrepancy_positive: 対象量が正であること、または正側の評価を示す。\<close>
corollary binary_logistic_low_discrepancy_positive:
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and xs_order: "xs \<in> binary_orders n N"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and prefix_discrepancy: "\<And>j. j \<le> N \<Longrightarrow>
      abs (prefix_sum (binary_innovation (real n / real N) xs) j) \<le> D"
    and positive_margin:
      "eta * D < mean_logistic_state eta (real n / real N) N"
  shows "0 < binary_logistic_state eta (real n / real N) xs N"
  using binary_logistic_prefix_discrepancy_control(2)
    [OF N_positive sample_size xs_order eta_nonnegative eta_at_most_four
      prefix_discrepancy] positive_margin
  by linarith

text \<open>curriculum_momentum_effective_attack_eventually: 十分大きな段階で成立する評価を示す。\<close>
lemma curriculum_momentum_effective_attack_eventually:
  fixes mu :: real
  assumes mu_nonnegative: "0 \<le> mu" and mu_less_one: "mu < 1"
  shows "\<forall>\<^sub>F k in sequentially.
    attack_state (momentum_effective_step (curriculum_learning_rate k) mu)
      (curriculum_anchor_count k) (curriculum_tail_count k) < -1"
proof -
  let ?d = "1 - mu"
  let ?C = "(exp (1::real) - 1) / ?d"
  let ?K = "\<lambda>k. real (curriculum_scale k)"
  let ?h = "\<lambda>k. momentum_effective_step (curriculum_learning_rate k) mu"
  let ?A = "\<lambda>k. ln (1 + real (curriculum_anchor_count k) *
    (exp (?h k) - 1))"
  have d_positive: "0 < ?d" using mu_less_one by linarith
  have C_nonnegative: "0 \<le> ?C"
    using d_positive by (intro divide_nonneg_nonneg) simp_all
  have effective_limit: "(?h \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_momentum_effective_step_tendsto_zero[OF mu_less_one])
  have effective_less: "\<forall>\<^sub>F k in sequentially. ?h k < 1"
    using order_tendstoD(2)[OF effective_limit, of 1] by simp
  have effective_small: "\<forall>\<^sub>F k in sequentially. ?h k \<le> 1"
  proof (rule eventually_mono[OF effective_less])
    fix k assume "?h k < 1"
    then show "?h k \<le> 1" by linarith
  qed
  have upper_bound: "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k \<le> (ln (1 + ?C) + 2 * ln (?K k)) / ?K k"
  proof (rule eventually_mono[OF effective_small])
    fix k assume h_small: "?h k \<le> 1"
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have K_square_one: "1 \<le> (?K k)^2"
      using curriculum_scale_at_least_four[of k] by simp
    have h_positive: "0 < ?h k"
      unfolding momentum_effective_step_def
      using curriculum_learning_rate_positive[of k] d_positive
      by (intro divide_pos_pos)
    have secant: "exp (?h k) - 1 \<le> ?h k * (exp 1 - 1)"
    proof -
      have "exp ((?h k) * 1) \<le> 1 + (?h k) * (exp 1 - 1)"
        by (rule exp_secant) (use h_positive h_small in linarith)+
      then show ?thesis by simp
    qed
    have anchor_le_population:
      "curriculum_anchor_count k \<le> curriculum_population k"
      using curriculum_counts[of k] by linarith
    have exponential_nonnegative: "0 \<le> exp (?h k) - 1"
      using h_positive by simp
    have scaled_anchor:
      "real (curriculum_anchor_count k) * (exp (?h k) - 1) \<le>
        (?K k)^2 * ?C"
    proof -
      have "real (curriculum_anchor_count k) * (exp (?h k) - 1) \<le>
          real (curriculum_population k) * (?h k * (exp 1 - 1))"
        using anchor_le_population secant exponential_nonnegative
        by (meson mult_mono of_nat_0_le_iff of_nat_mono)
      also have "\<dots> = (?K k)^2 * ?C"
        unfolding momentum_effective_step_def
        using curriculum_population_learning_mass[of k] d_positive
        by (simp add: field_simps; algebra)
      finally show ?thesis .
    qed
    have expanded_upper:
      "(1 + ?C) * (?K k)^2 = (?K k)^2 + ?C * (?K k)^2"
      by algebra
    have scaled_anchor_commuted:
      "real (curriculum_anchor_count k) * (exp (?h k) - 1) \<le>
        ?C * (?K k)^2"
      using scaled_anchor by (simp add: mult.commute)
    have argument_upper:
      "1 + real (curriculum_anchor_count k) * (exp (?h k) - 1) \<le>
        (1 + ?C) * (?K k)^2"
      using scaled_anchor_commuted K_square_one expanded_upper by linarith
    have product_nonnegative:
      "0 \<le> real (curriculum_anchor_count k) * (exp (?h k) - 1)"
      by (rule mult_nonneg_nonneg) (use exponential_nonnegative in simp_all)
    have argument_positive:
      "0 < 1 + real (curriculum_anchor_count k) * (exp (?h k) - 1)"
      using product_nonnegative by linarith
    have log_upper: "?A k \<le> ln ((1 + ?C) * (?K k)^2)"
      by (rule ln_mono[OF argument_upper argument_positive])
    have coefficient_positive: "0 < 1 + ?C" using C_nonnegative by linarith
    have log_identity:
      "ln ((1 + ?C) * (?K k)^2) = ln (1 + ?C) + 2 * ln (?K k)"
      using coefficient_positive K_positive by (simp add: ln_mult ln_realpow)
    show "?A k / ?K k \<le> (ln (1 + ?C) + 2 * ln (?K k)) / ?K k"
      using log_upper log_identity K_positive by (simp add: divide_right_mono)
  qed
  have lower_bound: "\<forall>\<^sub>F k in sequentially. 0 \<le> ?A k / ?K k"
  proof (intro always_eventually allI)
    fix k
    have h_positive: "0 < ?h k"
      unfolding momentum_effective_step_def
      using curriculum_learning_rate_positive[of k] d_positive
      by (intro divide_pos_pos)
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have "0 \<le> ?A k" using h_positive by simp
    then show "0 \<le> ?A k / ?K k"
      using K_positive by (intro divide_nonneg_nonneg) simp_all
  qed
  have inverse_limit: "((\<lambda>k. 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using curriculum_tail_ratio_tendsto_zero
    by (simp add: curriculum_tail_ratio_exact)
  have constant_limit: "((\<lambda>k. ln (1 + ?C) / ?K k) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const inverse_limit, of "ln (1 + ?C)"]
    by (simp add: field_class.field_divide_inverse)
  have twice_log_limit: "((\<lambda>k. 2 * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
    using tendsto_mult[OF tendsto_const curriculum_log_scale_over_scale_tendsto_zero, of 2]
    by simp
  have upper_limit: "((\<lambda>k. (ln (1 + ?C) + 2 * ln (?K k)) / ?K k)
      \<longlongrightarrow> 0) sequentially"
  proof -
    have sum_limit: "((\<lambda>k. ln (1 + ?C) / ?K k +
        2 * (ln (?K k) / ?K k)) \<longlongrightarrow> 0) sequentially"
      using tendsto_add[OF constant_limit twice_log_limit] by simp
    show ?thesis using sum_limit
      by (simp add: field_class.field_divide_inverse algebra_simps)
  qed
  have normalized_limit: "((\<lambda>k. ?A k / ?K k) \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[OF lower_bound upper_bound tendsto_const upper_limit])
  have sum_limit: "((\<lambda>k. ?A k / ?K k + 1 / ?K k) \<longlongrightarrow> 0) sequentially"
    using tendsto_add[OF normalized_limit inverse_limit] by simp
  have target_denominator_positive: "0 < ?d * (1 + exp (1::real))"
    by (rule mult_pos_pos) (use d_positive exp_gt_zero[of "1::real"] in linarith)+
  have target_positive: "0 < 1 / (?d * (1 + exp (1::real)))"
    by (rule divide_pos_pos) (use target_denominator_positive in simp_all)
  have eventual_normalized: "\<forall>\<^sub>F k in sequentially.
      ?A k / ?K k + 1 / ?K k < 1 / (?d * (1 + exp 1))"
    using order_tendstoD(2)[OF sum_limit, of "1 / (?d * (1 + exp 1))"]
      target_positive by simp
  show ?thesis
  proof (rule eventually_mono[OF eventual_normalized])
    fix k assume normalized: "?A k / ?K k + 1 / ?K k <
      1 / (?d * (1 + exp 1))"
    have K_positive: "0 < ?K k"
      using curriculum_scale_at_least_four[of k] by simp
    have normalized_identity:
      "?A k / ?K k + 1 / ?K k = (?A k + 1) / ?K k"
      unfolding field_class.field_divide_inverse by algebra
    have first_takeover:
      "?A k + 1 < ?K k / (?d * (1 + exp 1))"
      using normalized normalized_identity K_positive
      by (simp add: pos_divide_less_eq)
    have effective_tail_identity:
      "?h k * real (curriculum_tail_count k) = ?K k / ?d"
    proof -
      have "?h k * real (curriculum_tail_count k) =
          (curriculum_learning_rate k * real (curriculum_tail_count k)) *
            inverse ?d"
        unfolding momentum_effective_step_def field_class.field_divide_inverse
        by algebra
      also have "\<dots> = ?K k * inverse ?d"
        using curriculum_effective_tail_mass[of k] by simp
      also have "\<dots> = ?K k / ?d"
        unfolding field_class.field_divide_inverse ..
      finally show ?thesis .
    qed
    have denominator_nonzero: "1 + exp (1::real) \<noteq> 0"
      using exp_gt_zero[of "1::real"] by linarith
    have target_identity:
      "(?K k / ?d) / (1 + exp 1) = ?K k / (?d * (1 + exp 1))"
      using d_positive denominator_nonzero by (simp add: field_simps)
    have takeover: "?A k + 1 <
        ?h k * real (curriculum_tail_count k) / (1 + exp 1)"
      using first_takeover effective_tail_identity target_identity by simp
    have h_positive: "0 < ?h k"
      unfolding momentum_effective_step_def
      using curriculum_learning_rate_positive[of k] d_positive
      by (intro divide_pos_pos)
    have anchor_bound: "anchor_state (?h k) (curriculum_anchor_count k) \<le> ?A k"
      by (rule anchor_log_bound) (use h_positive in linarith)
    have decrement_identity:
      "real (curriculum_tail_count k) * (?h k * (1 / (1 + exp 1))) =
        ?h k * real (curriculum_tail_count k) / (1 + exp 1)"
      unfolding field_class.field_divide_inverse by algebra
    have takeover_form: "?A k - real (curriculum_tail_count k) *
        (?h k * (1 / (1 + exp 1))) < -1"
      using takeover decrement_identity by linarith
    show "attack_state (?h k) (curriculum_anchor_count k)
        (curriculum_tail_count k) < -1"
      by (rule logarithmic_anchor_bound_implies_inversion
        [OF h_positive anchor_bound takeover_form])
  qed
qed

text \<open>curriculum_fixed_momentum_attack_eventually_negative: 十分大きな段階で成立する評価を示す。\<close>
theorem curriculum_fixed_momentum_attack_eventually_negative:
  fixes mu :: real
  assumes mu_nonnegative: "0 \<le> mu" and mu_less_one: "mu < 1"
  shows "\<forall>\<^sub>F k in sequentially.
    momentum_w_state (curriculum_learning_rate k) mu
      (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
      (curriculum_population k) < 0"
proof -
  have effective_limit:
    "((\<lambda>k. momentum_effective_step (curriculum_learning_rate k) mu)
      \<longlongrightarrow> 0) sequentially"
    by (rule curriculum_momentum_effective_step_tendsto_zero[OF mu_less_one])
  have effective_small: "\<forall>\<^sub>F k in sequentially.
      momentum_effective_step (curriculum_learning_rate k) mu \<le> 4"
  proof -
    have strict: "\<forall>\<^sub>F k in sequentially.
        momentum_effective_step (curriculum_learning_rate k) mu < 4"
      using order_tendstoD(2)[OF effective_limit, of 4] by simp
    show ?thesis
    proof (rule eventually_mono[OF strict])
      fix k assume "momentum_effective_step (curriculum_learning_rate k) mu < 4"
      then show "momentum_effective_step (curriculum_learning_rate k) mu \<le> 4"
        by linarith
    qed
  qed
  have error_small: "\<forall>\<^sub>F k in sequentially.
      momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    by (rule curriculum_momentum_transfer_error_eventually_small_general
      [OF mu_less_one]) simp
  have attack_eventual: "\<forall>\<^sub>F k in sequentially. attack_state
      (momentum_effective_step (curriculum_learning_rate k) mu)
      (curriculum_anchor_count k) (curriculum_tail_count k) < -1"
    by (rule curriculum_momentum_effective_attack_eventually
      [OF mu_nonnegative mu_less_one])
  have small_and_error: "\<forall>\<^sub>F k in sequentially.
      momentum_effective_step (curriculum_learning_rate k) mu \<le> 4 \<and>
      momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    by (rule eventually_conj[OF effective_small error_small])
  have eventual_conditions: "\<forall>\<^sub>F k in sequentially.
      attack_state (momentum_effective_step (curriculum_learning_rate k) mu)
        (curriculum_anchor_count k) (curriculum_tail_count k) < -1 \<and>
      momentum_effective_step (curriculum_learning_rate k) mu \<le> 4 \<and>
      momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    by (rule eventually_conj[OF attack_eventual small_and_error])
  show ?thesis
  proof (rule eventually_mono[OF eventual_conditions])
    fix k
    assume conditions: "attack_state
        (momentum_effective_step (curriculum_learning_rate k) mu)
        (curriculum_anchor_count k) (curriculum_tail_count k) < -1 \<and>
      momentum_effective_step (curriculum_learning_rate k) mu \<le> 4 \<and>
      momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
    have counts_reordered:
      "curriculum_anchor_count k + curriculum_tail_count k =
        curriculum_population k"
      using curriculum_counts[of k] by (simp add: add.commute)
    have exact: "binary_logistic_state
        (momentum_effective_step (curriculum_learning_rate k) mu)
        (real (curriculum_anchor_count k) / real (curriculum_population k))
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_anchor_count k + curriculum_tail_count k) =
      attack_state (momentum_effective_step (curriculum_learning_rate k) mu)
        (curriculum_anchor_count k) (curriculum_tail_count k)"
      by (rule binary_logistic_state_attack_order)
    have exact_population: "binary_logistic_state
        (momentum_effective_step (curriculum_learning_rate k) mu)
        (real (curriculum_anchor_count k) / real (curriculum_population k))
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k) =
      attack_state (momentum_effective_step (curriculum_learning_rate k) mu)
        (curriculum_anchor_count k) (curriculum_tail_count k)"
      using exact counts_reordered by simp
    have attack_upper: "attack_state
        (momentum_effective_step (curriculum_learning_rate k) mu)
        (curriculum_anchor_count k) (curriculum_tail_count k) \<le> -1"
      using conditions by linarith
    have attack_reference: "binary_logistic_state
        (momentum_effective_step (curriculum_learning_rate k) mu)
        (real (curriculum_anchor_count k) / real (curriculum_population k))
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k) \<le> -1"
      using exact_population attack_upper by simp
    have effective_bound:
      "momentum_effective_step (curriculum_learning_rate k) mu \<le> 4"
      using conditions by simp
    have error_bound: "momentum_transfer_error (curriculum_learning_rate k) mu
        (curriculum_population k) < 1"
      using conditions by simp
    have rate_nonnegative: "0 \<le> curriculum_learning_rate k"
      using curriculum_learning_rate_positive[of k] by linarith
    show "momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k) < 0"
      by (rule momentum_negative_margin_transfer
        [where q="real (curriculum_anchor_count k) / real (curriculum_population k)"
          and G=1, OF rate_nonnegative mu_nonnegative mu_less_one
          effective_bound attack_reference error_bound])
  qed
qed

text \<open>curriculum_fixed_momentum_attack_metrics_eventually: 十分大きな段階で成立する評価を示す。\<close>
lemma curriculum_fixed_momentum_attack_metrics_eventually:
  fixes mu :: real
  assumes mu_nonnegative: "0 \<le> mu" and mu_less_one: "mu < 1"
  shows "\<forall>\<^sub>F k in sequentially.
    clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
    clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)) = curriculum_tail_ratio k"
proof -
  show ?thesis
  proof (rule eventually_mono[OF curriculum_fixed_momentum_attack_eventually_negative
      [OF mu_nonnegative mu_less_one]])
    fix k
    assume negative: "momentum_w_state (curriculum_learning_rate k) mu
      (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
      (curriculum_population k) < 0"
    show "clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)) = 1 - curriculum_tail_ratio k \<and>
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k)) = curriculum_tail_ratio k"
      by (intro conjI clean_test_risk_negative[OF negative]
        clean_test_auc_negative[OF negative])
  qed
qed

text \<open>curriculum_fixed_momentum_attack_metric_limits: リスクと AUC の極限をまとめて示す。\<close>
theorem curriculum_fixed_momentum_attack_metric_limits:
  fixes mu :: real
  assumes mu_nonnegative: "0 \<le> mu" and mu_less_one: "mu < 1"
  shows "((\<lambda>k.
    (clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)),
     clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k)))) \<longlongrightarrow> (1, 0)) sequentially"
proof (intro tendsto_Pair)
  note metrics = curriculum_fixed_momentum_attack_metrics_eventually
    [OF mu_nonnegative mu_less_one]
  show "((\<lambda>k. clean_test_risk (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))) \<longlongrightarrow> 1) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_clean_metric_limits(1)])
    show "\<forall>\<^sub>F k in sequentially. 1 - curriculum_tail_ratio k =
      clean_test_risk (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))"
      using metrics by eventually_elim simp
  qed
  show "((\<lambda>k. clean_test_auc (curriculum_tail_ratio k)
      (momentum_w_state (curriculum_learning_rate k) mu
        (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
        (curriculum_population k))) \<longlongrightarrow> 0) sequentially"
  proof (rule Lim_transform_eventually[OF curriculum_tail_ratio_tendsto_zero])
    show "\<forall>\<^sub>F k in sequentially. curriculum_tail_ratio k =
      clean_test_auc (curriculum_tail_ratio k)
        (momentum_w_state (curriculum_learning_rate k) mu
          (attack_order (curriculum_anchor_count k) (curriculum_tail_count k))
          (curriculum_population k))"
      using metrics by eventually_elim simp
  qed
qed

end
