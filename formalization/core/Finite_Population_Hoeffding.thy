theory Finite_Population_Hoeffding
  imports Order_Only_Inversion "HOL-Combinatorics.Multiset_Permutations"

begin
section \<open>Finite uniform probability\<close>

definition uniform_probability :: "'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "uniform_probability \<Omega> E = real (card (\<Omega> \<inter> E)) / real (card \<Omega>)"

definition k_subsets :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "k_subsets U k = {S. S \<subseteq> U \<and> card S = k}"

definition indexed_permutations :: "nat \<Rightarrow> nat list set" where
  "indexed_permutations N = permutations_of_set {..<N}"

definition uniform_permutation_probability :: "nat \<Rightarrow> nat list set \<Rightarrow> real" where
  "uniform_permutation_probability N E = uniform_probability (indexed_permutations N) E"

definition anchor_prefix_count :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "anchor_prefix_count n xs k = length (filter (\<lambda>i. i < n) (take k xs))"

definition centered_prefix :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> real" where
  "centered_prefix n N xs k =
     real (anchor_prefix_count n xs k) - real k * (real n / real N)"

definition max_centered_prefix :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> real" where
  "max_centered_prefix n N xs = Max ((\<lambda>k. abs (centered_prefix n N xs k)) ` {1..N})"

lemma card_k_subsets:
  assumes "finite U"
  shows "card (k_subsets U k) = card U choose k"
  unfolding k_subsets_def using n_subsets[OF assms] .

lemma indexed_permutation_support:
  assumes "xs \<in> indexed_permutations N"
  shows "distinct xs" and "set xs = {..<N}" and "length xs = N"
  using assms unfolding indexed_permutations_def
  by (auto dest: permutations_of_setD length_finite_permutations_of_set)

lemma card_indexed_permutations [simp]:
  "card (indexed_permutations N) = fact N"
  unfolding indexed_permutations_def by simp

definition super_k_subsets :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set set" where
  "super_k_subsets U R k = {S \<in> k_subsets U k. R \<subseteq> S}"

lemma card_super_k_subsets:
  assumes finite_U: "finite U"
    and subset: "R \<subseteq> U"
    and size: "card R \<le> k"
  shows "card (super_k_subsets U R k) =
         (card U - card R) choose (k - card R)"
proof -
  have finite_R: "finite R"
    using finite_U subset finite_subset by blast
  have bij:
    "bij_betw (\<lambda>S. S - R) (super_k_subsets U R k)
       (k_subsets (U - R) (k - card R))"
  proof (rule bij_betwI[where g = "\<lambda>T. R \<union> T"])
    show "(\<lambda>S. S - R) \<in> super_k_subsets U R k \<rightarrow>
        k_subsets (U - R) (k - card R)"
    proof (intro Pi_I)
      fix S
      assume S: "S \<in> super_k_subsets U R k"
      have R_subset_S: "R \<subseteq> S"
        using S by (simp add: super_k_subsets_def)
      have S_subset_U: "S \<subseteq> U"
        using S by (auto simp: super_k_subsets_def k_subsets_def)
      have card_diff: "card (S - R) = card S - card R"
        using finite_R R_subset_S by (rule card_Diff_subset)
      show "S - R \<in> k_subsets (U - R) (k - card R)"
        unfolding k_subsets_def
      proof (intro CollectI conjI)
        show "S - R \<subseteq> U - R"
          using S_subset_U by auto
        show "card (S - R) = k - card R"
          using S card_diff by (auto simp: super_k_subsets_def k_subsets_def)
      qed
    qed
    show "(\<lambda>T. R \<union> T) \<in> k_subsets (U - R) (k - card R) \<rightarrow>
        super_k_subsets U R k"
    proof (intro Pi_I)
      fix T
      assume T: "T \<in> k_subsets (U - R) (k - card R)"
      have T_subset: "T \<subseteq> U - R" and card_T: "card T = k - card R"
        using T by (auto simp: k_subsets_def)
      have finite_T: "finite T"
        using finite_U T_subset by (auto dest: finite_subset)
      have disjoint: "R \<inter> T = {}"
        using T_subset by blast
      have card_union: "card (R \<union> T) = k"
      proof -
        have "card (R \<union> T) = card R + card T"
          using finite_R finite_T disjoint by (simp add: card_Un_disjoint)
        also have "\<dots> = k"
          using card_T size by simp
        finally show ?thesis .
      qed
      show "R \<union> T \<in> super_k_subsets U R k"
        unfolding super_k_subsets_def
      proof (intro CollectI conjI)
        show "R \<union> T \<in> k_subsets U k"
          using subset T_subset card_union
          by (auto simp: k_subsets_def)
        show "R \<subseteq> R \<union> T" by simp
      qed
    qed
    show "R \<union> (S - R) = S"
      if S: "S \<in> super_k_subsets U R k" for S
    proof -
      have "R \<subseteq> S"
        using S by (simp add: super_k_subsets_def)
      show ?thesis
      proof (rule subset_antisym)
        show "R \<union> (S - R) \<subseteq> S"
          using \<open>R \<subseteq> S\<close> by auto
        show "S \<subseteq> R \<union> (S - R)" by auto
      qed
    qed
    show "(R \<union> T) - R = T"
      if T: "T \<in> k_subsets (U - R) (k - card R)" for T
    proof -
      have "T \<subseteq> U - R"
        using T by (simp add: k_subsets_def)
      show ?thesis
      proof (rule subset_antisym)
        show "(R \<union> T) - R \<subseteq> T"
          using \<open>T \<subseteq> U - R\<close> by auto
        show "T \<subseteq> (R \<union> T) - R"
          using \<open>T \<subseteq> U - R\<close> by auto
      qed
    qed
  qed
  have "card (super_k_subsets U R k) =
        card (k_subsets (U - R) (k - card R))"
    using bij by (rule bij_betw_same_card)
  also have "\<dots> = (card U - card R) choose (k - card R)"
    using finite_U finite_R subset
    by (simp add: card_k_subsets card_Diff_subset)
  finally show ?thesis .
qed

fun falling_ratio :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "falling_ratio n N 0 = 1"
| "falling_ratio n N (Suc r) =
     falling_ratio n N r * (real (n - r) / real (N - r))"

lemma falling_ratio_nonneg:
  assumes "r \<le> n" and "n \<le> N"
  shows "0 \<le> falling_ratio n N r"
  using assms
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have "r \<le> n" using Suc.prems by simp
  then show ?case
    using Suc.IH Suc.prems
    by simp
qed

lemma falling_ratio_step_le:
  assumes "r < n" and "n \<le> N" and "0 < N"
  shows "real (n - r) / real (N - r) \<le> real n / real N"
proof -
  have rN: "r < N" using assms by linarith
  have denominators: "0 < real (N - r)" "0 < real N"
    using rN assms by simp_all
  have denominator_ne: "real (N - r) \<noteq> 0" "real N \<noteq> 0"
    using denominators by simp_all
  have nN_real: "real n \<le> real N"
    using assms by simp
  have scaled: "real r * real n \<le> real r * real N"
    using nN_real by (rule mult_left_mono) simp
  have cross: "real (n - r) * real N \<le> real n * real (N - r)"
  proof -
    have "(real n - real r) * real N =
        real n * real N - real r * real N"
      by algebra
    also have "\<dots> \<le> real n * real N - real r * real n"
      using scaled by linarith
    also have "\<dots> = real n * (real N - real r)"
      by algebra
    finally show ?thesis
      using assms by simp
  qed
  show ?thesis
    unfolding frac_le_eq[OF denominator_ne]
  proof (rule divide_nonpos_nonneg)
    show "real (n - r) * real N -
        real n * real (N - r) \<le> 0"
      using cross by linarith
    show "0 \<le> real (N - r) * real N"
      using denominators by (intro mult_nonneg_nonneg) linarith+
  qed
qed

lemma falling_ratio_le_power:
  assumes "r \<le> n" and "n \<le> N" and "0 < N"
  shows "falling_ratio n N r \<le> (real n / real N) ^ r"
  using assms
proof (induction r)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have r_less_n: "r < n" using Suc.prems by simp
  have ratio_nonneg: "0 \<le> real n / real N"
    using Suc.prems by simp
  have factor_nonneg: "0 \<le> real (n - r) / real (N - r)"
    by simp
  have "falling_ratio n N (Suc r) =
      falling_ratio n N r * (real (n - r) / real (N - r))"
    by simp
  also have "\<dots> \<le> (real n / real N) ^ r *
      (real (n - r) / real (N - r))"
    using Suc.IH Suc.prems factor_nonneg
    by (intro mult_right_mono) simp_all
  also have "\<dots> \<le> (real n / real N) ^ r * (real n / real N)"
    using falling_ratio_step_le[OF r_less_n Suc.prems(2,3)]
    by (intro mult_left_mono) simp_all
  also have "\<dots> = (real n / real N) ^ Suc r"
    by simp
  finally show ?case .
qed

lemma choose_ratio_eq_falling_ratio:
  assumes "r \<le> n" and "n \<le> N"
  shows "real ((N - r) choose (n - r)) / real (N choose n) =
         falling_ratio n N r"
  using assms
proof (induction r arbitrary: n N)
  case 0
  show ?case using zero_less_binomial[OF "0.prems"(2)] by simp
next
  case (Suc r)
  have r_less_n: "r < n" and r_less_N: "r < N"
    using Suc.prems by simp_all
  have denominator_ne: "real (N - r) \<noteq> 0"
    using r_less_N by simp
  have absorb_nat:
    "(n - r) * ((N - r) choose (n - r)) =
     (N - r) * (((N - r) - 1) choose ((n - r) - 1))"
    using times_binomial_minus1_eq[of "n - r" "N - r"] r_less_n
    by simp
  have absorb:
    "real (n - r) * real ((N - r) choose (n - r)) =
     real (N - r) * real ((N - Suc r) choose (n - Suc r))"
  proof -
    have cast_absorb:
      "real ((n - r) * ((N - r) choose (n - r))) =
       real ((N - r) * (((N - r) - 1) choose ((n - r) - 1)))"
      using absorb_nat by simp
    show ?thesis
      using cast_absorb r_less_n r_less_N by simp
  qed
  have step:
    "real ((N - Suc r) choose (n - Suc r)) =
     real (n - r) * real ((N - r) choose (n - r)) / real (N - r)"
  proof (subst nonzero_eq_divide_eq[OF denominator_ne])
    show "real ((N - Suc r) choose (n - Suc r)) * real (N - r) =
          real (n - r) * real ((N - r) choose (n - r))"
      using absorb by (simp add: mult.commute)
  qed
  have "real ((N - Suc r) choose (n - Suc r)) / real (N choose n) =
      (real ((N - r) choose (n - r)) / real (N choose n)) *
      (real (n - r) / real (N - r))"
    unfolding step by algebra
  also have "\<dots> = falling_ratio n N r *
      (real (n - r) / real (N - r))"
    using Suc.IH Suc.prems by simp
  also have "\<dots> = falling_ratio n N (Suc r)"
    by simp
  finally show ?case .
qed

lemma uniform_subset_cylinder_bound:
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and contained: "R \<subseteq> U"
    and cylinder_size: "card R \<le> n"
  shows "uniform_probability (k_subsets U n) (super_k_subsets U R n)
       \<le> (real n / real (card U)) ^ card R"
proof -
  have finite_R: "finite R"
    using finite_U contained finite_subset by blast
  have event_subset:
    "super_k_subsets U R n \<subseteq> k_subsets U n"
    by (auto simp: super_k_subsets_def)
  have denominator_pos: "0 < real (card U choose n)"
    using zero_less_binomial[OF sample_size] by simp
  have probability_eq:
    "uniform_probability (k_subsets U n) (super_k_subsets U R n) =
     real ((card U - card R) choose (n - card R)) /
     real (card U choose n)"
    unfolding uniform_probability_def
    using finite_U contained cylinder_size sample_size event_subset
    by (simp add: card_k_subsets card_super_k_subsets Int_absorb1)
  have ratio_eq:
    "real ((card U - card R) choose (n - card R)) /
       real (card U choose n) =
     falling_ratio n (card U) (card R)"
    using choose_ratio_eq_falling_ratio[OF cylinder_size sample_size] .
  show ?thesis
    unfolding probability_eq ratio_eq
    using falling_ratio_le_power[OF cylinder_size sample_size nonempty_U] .
qed

definition uniform_expectation :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" where
  "uniform_expectation Omega f = sum f Omega / real (card Omega)"

definition subset_count :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat" where
  "subset_count K S = card (K \<inter> S)"

lemma sum_Pow_card:
  fixes c :: real
  assumes "finite A"
  shows "sum (\<lambda>R. c ^ card R) (Pow A) = (1 + c) ^ card A"
  using assms
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x A)
  have inj: "inj_on (insert x) (Pow A)"
    using insert.hyps by (auto simp: inj_on_def)
  have disjoint: "Pow A \<inter> insert x ` Pow A = {}"
    using insert.hyps by auto
  have image_sum:
    "sum (\<lambda>R. c ^ card R) (insert x ` Pow A) =
     c * sum (\<lambda>R. c ^ card R) (Pow A)"
  proof -
    have "sum (\<lambda>R. c ^ card R) (insert x ` Pow A) =
        sum ((\<lambda>R. c ^ card R) \<circ> insert x) (Pow A)"
      using inj by (rule sum.reindex)
    also have "... = sum (\<lambda>R. c * c ^ card R) (Pow A)"
    proof (rule sum.cong)
      show "Pow A = Pow A" by simp
      fix R
      assume "R \<in> Pow A"
      then have "finite R" "x \<notin> R"
        using insert.hyps by (auto dest: finite_subset)
      then show "((\<lambda>R. c ^ card R) \<circ> insert x) R =
          c * c ^ card R"
        by simp
    qed
    also have "... = c * sum (\<lambda>R. c ^ card R) (Pow A)"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  have "sum (\<lambda>R. c ^ card R) (Pow (insert x A)) =
      sum (\<lambda>R. c ^ card R) (Pow A) +
      sum (\<lambda>R. c ^ card R) (insert x ` Pow A)"
    unfolding Pow_insert
    by (rule sum.union_disjoint) (use insert.hyps disjoint in auto)
  also have "... = sum (\<lambda>R. c ^ card R) (Pow A) +
      c * sum (\<lambda>R. c ^ card R) (Pow A)"
    unfolding image_sum by simp
  also have "... = (1 + c) * (1 + c) ^ card A"
    by (simp add: insert.IH algebra_simps)
  also have "... = (1 + c) ^ card (insert x A)"
    using insert.hyps by simp
  finally show ?case .
qed
lemma exp_subset_count_expansion:
  fixes lambda :: real
  assumes finite_K: "finite K"
  shows "exp (lambda * real (subset_count K S)) =
    sum (\<lambda>R. if R \<subseteq> S then (exp lambda - 1) ^ card R else 0) (Pow K)"
proof -
  have finite_inter: "finite (K \<inter> S)"
    using finite_K by simp
  have finite_pow: "finite (Pow K)"
    using finite_K by simp  have restricted: "{R \<in> Pow K. R \<subseteq> S} = Pow (K \<inter> S)"
    by auto
  have filtered:
    "sum (\<lambda>R. if R \<subseteq> S then (exp lambda - 1) ^ card R else 0) (Pow K) =
     sum (\<lambda>R. (exp lambda - 1) ^ card R) (Pow (K \<inter> S))"
  proof -
    have "sum (\<lambda>R. (exp lambda - 1) ^ card R) {R \<in> Pow K. R \<subseteq> S} =
        sum (\<lambda>R. if R \<subseteq> S then (exp lambda - 1) ^ card R else 0) (Pow K)"
      using sum.inter_filter[OF finite_pow,
        of "\<lambda>R. (exp lambda - 1) ^ card R" "\<lambda>R. R \<subseteq> S"] .    then show ?thesis
      unfolding restricted by simp
  qed
  have "exp (lambda * real (subset_count K S)) =
      (exp lambda) ^ subset_count K S"
    by (simp add: exp_of_nat2_mult)
  also have "... = (1 + (exp lambda - 1)) ^ card (K \<inter> S)"
    by (simp add: subset_count_def)
  also have "... = sum (\<lambda>R. (exp lambda - 1) ^ card R) (Pow (K \<inter> S))"
    using sum_Pow_card[OF finite_inter, of "exp lambda - 1"] by simp
  also have "... = sum (\<lambda>R. if R \<subseteq> S then (exp lambda - 1) ^ card R else 0) (Pow K)"
    using filtered by simp
  finally show ?thesis .
qed

lemma sum_subset_indicator:
  fixes c :: real
  assumes finite_Omega: "finite Omega"
  shows "sum (\<lambda>S. if R \<subseteq> S then c else 0) Omega =
    real (card {S \<in> Omega. R \<subseteq> S}) * c"
proof -
  note h = sum.inter_filter[OF finite_Omega,
    of "\<lambda>_. c" "\<lambda>S. R \<subseteq> S"]
  show ?thesis
    using h by simp
qed
lemma uniform_subset_exp_moment:
  fixes lambda :: real
  assumes finite_U: "finite U"
    and finite_K: "finite K"
  shows "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) =
    sum (\<lambda>R. (exp lambda - 1) ^ card R *
      uniform_probability (k_subsets U n) (super_k_subsets U R n)) (Pow K)"
proof -
  have finite_Omega: "finite (k_subsets U n)"
  proof (rule finite_subset[where B = "Pow U"])
    show "k_subsets U n \<subseteq> Pow U"
      by (auto simp: k_subsets_def)
    show "finite (Pow U)"
      using finite_U by simp
  qed
  have expanded:
    "sum (\<lambda>S. exp (lambda * real (subset_count K S))) (k_subsets U n) =
     sum (\<lambda>R. real (card (super_k_subsets U R n)) *
       (exp lambda - 1) ^ card R) (Pow K)"
  proof -
    have "sum (\<lambda>S. exp (lambda * real (subset_count K S))) (k_subsets U n) =
        sum (\<lambda>S. sum (\<lambda>R. if R \<subseteq> S then
          (exp lambda - 1) ^ card R else 0) (Pow K)) (k_subsets U n)"
    proof (rule sum.cong)
      show "k_subsets U n = k_subsets U n" by simp
      fix S
      assume "S \<in> k_subsets U n"
      show "exp (lambda * real (subset_count K S)) =
          sum (\<lambda>R. if R \<subseteq> S then
            (exp lambda - 1) ^ card R else 0) (Pow K)"
        using exp_subset_count_expansion[OF finite_K] .
    qed
    also have "... = sum (\<lambda>R. sum (\<lambda>S. if R \<subseteq> S then
        (exp lambda - 1) ^ card R else 0) (k_subsets U n)) (Pow K)"
      by (rule sum.swap)
    also have "... = sum (\<lambda>R. real (card (super_k_subsets U R n)) *
        (exp lambda - 1) ^ card R) (Pow K)"
    proof (rule sum.cong)
      show "Pow K = Pow K" by simp
      fix R
      assume "R \<in> Pow K"
      have event_eq: "{S \<in> k_subsets U n. R \<subseteq> S} =
          super_k_subsets U R n"
        by (auto simp: super_k_subsets_def)
      show "sum (\<lambda>S. if R \<subseteq> S then
          (exp lambda - 1) ^ card R else 0) (k_subsets U n) =
        real (card (super_k_subsets U R n)) * (exp lambda - 1) ^ card R"
        using sum_subset_indicator[OF finite_Omega,
          of R "(exp lambda - 1) ^ card R"]
        unfolding event_eq .
    qed
    finally show ?thesis .
  qed
  have event_subset: "super_k_subsets U R n \<subseteq> k_subsets U n" for R
    by (auto simp: super_k_subsets_def)
  have "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) =
      sum (\<lambda>R. real (card (super_k_subsets U R n)) *
        (exp lambda - 1) ^ card R) (Pow K) /
      real (card (k_subsets U n))"
    unfolding uniform_expectation_def expanded by simp
  also have "... = sum (\<lambda>R. (exp lambda - 1) ^ card R *
      (real (card (super_k_subsets U R n)) /
       real (card (k_subsets U n)))) (Pow K)"
    by (simp add: sum_divide_distrib algebra_simps)
  also have "... = sum (\<lambda>R. (exp lambda - 1) ^ card R *
      uniform_probability (k_subsets U n) (super_k_subsets U R n)) (Pow K)"
  proof (rule sum.cong)
    show "Pow K = Pow K" by simp
    fix R
    assume "R \<in> Pow K"
    show "(exp lambda - 1) ^ card R *
        (real (card (super_k_subsets U R n)) / real (card (k_subsets U n))) =
      (exp lambda - 1) ^ card R *
        uniform_probability (k_subsets U n) (super_k_subsets U R n)"
      unfolding uniform_probability_def
      using event_subset[of R] by (simp add: Int_absorb1)
  qed
  finally show ?thesis .
qed

lemma uniform_subset_exp_moment_bound:
  fixes lambda :: real
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and finite_K: "finite K"
    and K_subset: "K \<subseteq> U"
    and lambda_nonneg: "0 \<le> lambda"
  shows "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) \<le>
    (1 + (real n / real (card U)) * (exp lambda - 1)) ^ card K"
proof -
  let ?c = "exp lambda - 1"
  let ?p = "real n / real (card U)"
  have c_nonneg: "0 \<le> ?c"
  proof -
    have "1 \<le> exp lambda"
      using lambda_nonneg exp_mono[of 0 lambda] by simp
    then show ?thesis by linarith
  qed
  have p_nonneg: "0 \<le> ?p"
    by simp
  have moment:
    "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) =
     sum (\<lambda>R. ?c ^ card R *
       uniform_probability (k_subsets U n) (super_k_subsets U R n)) (Pow K)"
    using uniform_subset_exp_moment[OF finite_U finite_K] .
  have term_bound: "?c ^ card R *
      uniform_probability (k_subsets U n) (super_k_subsets U R n) \<le>
      ?c ^ card R * ?p ^ card R" if R: "R \<in> Pow K" for R
  proof (cases "card R \<le> n")
    case True
    have R_subset: "R \<subseteq> U"
      using R K_subset by auto
    have probability_bound:
      "uniform_probability (k_subsets U n) (super_k_subsets U R n) \<le>
       ?p ^ card R"
      using uniform_subset_cylinder_bound[OF finite_U nonempty_U sample_size
        R_subset True] .
    show ?thesis
      using probability_bound c_nonneg
      by (intro mult_left_mono) simp_all
  next
    case False
    have finite_R: "finite R"
      using R finite_K by (auto dest: finite_subset)
    have event_empty: "super_k_subsets U R n = {}"
    proof (rule ccontr)
      assume "super_k_subsets U R n \<noteq> {}"
      then obtain S where S: "S \<in> super_k_subsets U R n"
        by blast
      have "R \<subseteq> S" "card S = n" "finite S"
        using S finite_U
        by (auto simp: super_k_subsets_def k_subsets_def dest: finite_subset)
      then have "card R \<le> n"
        using finite_R card_mono by blast
      with False show False by simp
    qed
    show ?thesis
      unfolding event_empty uniform_probability_def
      using c_nonneg p_nonneg by simp
  qed
  have "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) \<le>
      sum (\<lambda>R. ?c ^ card R * ?p ^ card R) (Pow K)"
    unfolding moment
    by (rule sum_mono) (use term_bound in auto)
  also have "... = sum (\<lambda>R. (?c * ?p) ^ card R) (Pow K)"
    by (rule sum.cong) (simp_all flip: power_mult_distrib)
  also have "... = (1 + ?c * ?p) ^ card K"
    using sum_Pow_card[OF finite_K, of "?c * ?p"] .
  also have "... = (1 + ?p * ?c) ^ card K"
    by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma finite_population_quadratic_bound:
  fixes x c :: real
  shows "x * (c - x) \<le> c\<^sup>2 / 4"
proof -
  have "x * (c - x) = -(x - c / 2)\<^sup>2 + c\<^sup>2 / 4"
    by (simp add: field_simps power2_eq_square)
  also have "... \<le> 0 + c\<^sup>2 / 4"
    by (intro add_mono) auto
  finally show ?thesis by simp
qed

lemma finite_population_Hoeffding_aux:
  fixes h p :: real
  assumes h_nonneg: "h \<ge> 0"
    and p_nonneg: "p \<ge> 0"
  defines "L \<equiv> (\<lambda>h. -h * p + ln (1 + p * (exp h - 1)))"
  shows "L h \<le> h\<^sup>2 / 8"
proof (cases "h = 0")
  case False
  hence h: "h > 0"
    using h_nonneg by simp
  define L' where "L' = (\<lambda>h. -p + p * exp h / (1 + p * (exp h - 1)))"
  define L'' where "L'' = (\<lambda>h. -(p\<^sup>2) * exp h * exp h /
    (1 + p * (exp h - 1))\<^sup>2 + p * exp h / (1 + p * (exp h - 1)))"
  define Ls where "Ls = (\<lambda>n. [L, L', L''] ! n)"
  have [simp]: "L 0 = 0" "L' 0 = 0"
    by (auto simp: L_def L'_def)
  have deriv_L: "(L has_real_derivative L' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have positive: "1 + p * (exp x - 1) > 0"
      using p_nonneg that
      by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      using positive
      unfolding L_def L'_def
      by (auto intro!: derivative_eq_intros)
  qed
  have deriv_L': "(L' has_real_derivative L'' x) (at x)" if "x \<in> {0..h}" for x
  proof -
    have positive: "1 + p * (exp x - 1) > 0"
      using p_nonneg that
      by (intro add_pos_nonneg mult_nonneg_nonneg) auto
    show ?thesis
      unfolding L'_def L''_def
      by (insert positive, (rule derivative_eq_intros refl | simp)+)
        (auto simp: divide_simps; algebra)
  qed
  have differentiable_chain:
    "\<forall>m t. m < 2 \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow>
      (Ls m has_real_derivative Ls (Suc m) t) (at t)"
    using deriv_L deriv_L'
    by (auto simp: Ls_def nth_Cons split: nat.splits)
  from Taylor[of 2 Ls L 0 h 0 h, OF _ _ differentiable_chain]
  obtain t where t: "t \<in> {0<..<h}" "L h = L'' t * h\<^sup>2 / 2"
    using h by (auto simp: Ls_def lessThan_nat_numeral)
  define u where "u = p * exp t / (1 + p * (exp t - 1))"
  have "L'' t = u * (1 - u)"
    by (simp add: L''_def u_def divide_simps; algebra)
  also have "... \<le> 1 / 4"
    using finite_population_quadratic_bound[of u 1] by simp
  finally have second_derivative_bound: "L'' t \<le> 1 / 4" .
  note t(2)
  also have "L'' t * h\<^sup>2 / 2 \<le> (1 / 4) * h\<^sup>2 / 2"
    using second_derivative_bound
    by (intro mult_right_mono divide_right_mono) auto
  finally show "L h \<le> h\<^sup>2 / 8" by simp
qed (auto simp: L_def)

lemma bernoulli_exp_bound:
  fixes h p :: real
  assumes h_nonneg: "0 \<le> h"
    and p_nonneg: "0 \<le> p"
  shows "exp (-h * p) * (1 + p * (exp h - 1)) \<le> exp (h\<^sup>2 / 8)"
proof -
  have positive: "0 < 1 + p * (exp h - 1)"
    using h_nonneg p_nonneg
    by (intro add_pos_nonneg mult_nonneg_nonneg) auto
  have exponent_bound:
    "-h * p + ln (1 + p * (exp h - 1)) \<le> h\<^sup>2 / 8"
    by (rule finite_population_Hoeffding_aux[OF h_nonneg p_nonneg])
  have exp_log:
    "exp (ln (1 + p * (exp h - 1))) = 1 + p * (exp h - 1)"
    using positive by simp
  have "exp (-h * p) * (1 + p * (exp h - 1)) =
      exp (-h * p) * exp (ln (1 + p * (exp h - 1)))"
    by (simp only: exp_log)
  also have "... = exp (-h * p + ln (1 + p * (exp h - 1)))"
    by (simp only: exp_add)
  also have "... \<le> exp (h\<^sup>2 / 8)"
    using exponent_bound by (rule exp_mono)
  finally show ?thesis .
qed

lemma uniform_expectation_mult_left:
  "uniform_expectation Omega (\<lambda>x. c * f x) =
    c * uniform_expectation Omega f"
  unfolding uniform_expectation_def
  by (simp add: sum_distrib_left)

lemma uniform_subset_centered_exp_moment_bound:
  fixes lambda :: real
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and finite_K: "finite K"
    and K_subset: "K \<subseteq> U"
    and lambda_nonneg: "0 \<le> lambda"
  shows "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * (real (subset_count K S) -
        real (card K) * (real n / real (card U))))) \<le>
    exp (real (card K) * lambda\<^sup>2 / 8)"
proof -
  let ?p = "real n / real (card U)"
  let ?k = "real (card K)"
  let ?base = "1 + ?p * (exp lambda - 1)"
  have p_nonneg: "0 \<le> ?p" by simp
  have raw_bound:
    "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * real (subset_count K S))) \<le>
      ?base ^ card K"
    using uniform_subset_exp_moment_bound[OF finite_U nonempty_U sample_size
      finite_K K_subset lambda_nonneg] .
  have centered_pointwise:
    "exp (lambda * (real (subset_count K S) - ?k * ?p)) =
      exp (-lambda * ?k * ?p) *
        exp (lambda * real (subset_count K S))" for S
  proof -
    have exponent_identity:
      "lambda * (real (subset_count K S) - ?k * ?p) =
       -lambda * ?k * ?p + lambda * real (subset_count K S)"
      by algebra
    show ?thesis
      unfolding exponent_identity by (simp only: exp_add)
  qed
  have centered_identity:
    "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * (real (subset_count K S) - ?k * ?p))) =
     exp (-lambda * ?k * ?p) *
       uniform_expectation (k_subsets U n)
         (\<lambda>S. exp (lambda * real (subset_count K S)))"
    proof -
    have function_identity:
      "(\<lambda>S. exp (lambda * (real (subset_count K S) - ?k * ?p))) =
       (\<lambda>S. exp (-lambda * ?k * ?p) *
         exp (lambda * real (subset_count K S)))"
      by (rule ext) (rule centered_pointwise)
    show ?thesis
      unfolding function_identity
      by (rule uniform_expectation_mult_left)
  qed
  have centered_factor_nonneg: "0 \<le> exp (-lambda * ?k * ?p)"
    by simp
  have scaled_raw_bound:
    "exp (-lambda * ?k * ?p) *
       uniform_expectation (k_subsets U n)
         (\<lambda>S. exp (lambda * real (subset_count K S))) \<le>
     exp (-lambda * ?k * ?p) * ?base ^ card K"
    using raw_bound centered_factor_nonneg by (rule mult_left_mono)
  have single_bound:
    "exp (-lambda * ?p) * ?base \<le> exp (lambda\<^sup>2 / 8)"
    using bernoulli_exp_bound[OF lambda_nonneg p_nonneg] .
  have exp_increment_nonneg: "0 \<le> exp lambda - 1"
  proof -
    have "1 \<le> exp lambda"
      using lambda_nonneg exp_mono[of 0 lambda] by simp
    then show ?thesis by linarith
  qed
  have base_nonneg: "0 \<le> ?base"
    using p_nonneg exp_increment_nonneg
    by (intro add_nonneg_nonneg mult_nonneg_nonneg) simp
  have powered_base_nonneg: "0 \<le> exp (-lambda * ?p) * ?base"
    using base_nonneg by (intro mult_nonneg_nonneg) simp_all
  have powered_bound:
    "(exp (-lambda * ?p) * ?base) ^ card K \<le>
      (exp (lambda\<^sup>2 / 8)) ^ card K"
    using single_bound powered_base_nonneg by (rule power_mono)
  have exp_power:
    "exp (-lambda * ?k * ?p) = exp (-lambda * ?p) ^ card K"
  proof -
    have exponent_identity:
      "-lambda * ?k * ?p = real (card K) * (-lambda * ?p)"
      by algebra
    have exp_nat:
      "exp (real (card K) * (-lambda * ?p)) =
        exp (-lambda * ?p) ^ card K"
      by (rule exp_of_nat_mult)
    show ?thesis
      unfolding exponent_identity using exp_nat .
  qed
  have left_power:
    "exp (-lambda * ?k * ?p) * ?base ^ card K =
      (exp (-lambda * ?p) * ?base) ^ card K"
    by (simp only: exp_power power_mult_distrib)
  have right_power:
    "(exp (lambda\<^sup>2 / 8)) ^ card K =
      exp (?k * lambda\<^sup>2 / 8)"
proof -
    have exp_nat:
      "exp (real (card K) * (lambda\<^sup>2 / 8)) =
        (exp (lambda\<^sup>2 / 8)) ^ card K"
      by (rule exp_of_nat_mult)
    have power_exp:
      "(exp (lambda\<^sup>2 / 8)) ^ card K =
        exp (real (card K) * (lambda\<^sup>2 / 8))"
      using exp_nat by (rule sym)
    have exponent_target:
      "exp (real (card K) * (lambda\<^sup>2 / 8)) =
        exp (?k * lambda\<^sup>2 / 8)"
      by (rule arg_cong[where f = exp]) algebra
    show ?thesis
      using power_exp exponent_target by (rule trans)
  qed  have "uniform_expectation (k_subsets U n)
      (\<lambda>S. exp (lambda * (real (subset_count K S) - ?k * ?p))) =
      exp (-lambda * ?k * ?p) *
        uniform_expectation (k_subsets U n)
          (\<lambda>S. exp (lambda * real (subset_count K S)))"
    using centered_identity .
  also have "... \<le> exp (-lambda * ?k * ?p) * ?base ^ card K"
    using scaled_raw_bound .
  also have "... = (exp (-lambda * ?p) * ?base) ^ card K"
    using left_power .
  also have "... \<le> (exp (lambda\<^sup>2 / 8)) ^ card K"
    using powered_bound .
  also have "... = exp (?k * lambda\<^sup>2 / 8)"
    using right_power .
  finally show ?thesis .
qed

lemma uniform_probability_exp_tail:
  fixes lambda u :: real
  assumes finite_Omega: "finite Omega"
    and nonempty_Omega: "Omega \<noteq> {}"
    and lambda_pos: "0 < lambda"
  shows "uniform_probability Omega {x. u \<le> f x} \<le>
    exp (-lambda * u) *
      uniform_expectation Omega (\<lambda>x. exp (lambda * f x))"
proof -
  let ?A = "Omega \<inter> {x. u \<le> f x}"
  let ?g = "\<lambda>x. exp (lambda * f x)"
  have finite_A: "finite ?A"
    using finite_Omega by simp
  have A_subset: "?A \<subseteq> Omega" by simp
  have point_bound: "exp (lambda * u) \<le> ?g x" if "x \<in> ?A" for x
  proof -
    have "lambda * u \<le> lambda * f x"
      using lambda_pos that by (intro mult_left_mono) auto
    then show ?thesis by (rule exp_mono)
  qed
  have event_sum_bound:
    "real (card ?A) * exp (lambda * u) \<le> sum ?g ?A"
  proof -
    have "sum (\<lambda>_. exp (lambda * u)) ?A \<le> sum ?g ?A"
      by (rule sum_mono) (use point_bound in auto)
    then show ?thesis
      using finite_A by simp
  qed
  have subset_sum_bound: "sum ?g ?A \<le> sum ?g Omega"
    using finite_Omega A_subset
    by (intro sum_mono2) simp_all
  have weighted_bound:
    "real (card ?A) * exp (lambda * u) \<le> sum ?g Omega"
    using event_sum_bound subset_sum_bound by (rule order_trans)
have exp_pos_u: "0 < exp (lambda * u)" by simp
  have card_bound:
    "real (card ?A) \<le> sum ?g Omega / exp (lambda * u)"
    using weighted_bound exp_pos_u
    by (simp add: pos_le_divide_eq mult.commute)
  have negative_product: "-lambda * u = -(lambda * u)" by algebra
  have exp_inverse: "exp (-lambda * u) = inverse (exp (lambda * u))"
    unfolding negative_product by (rule exp_minus)
have quotient_identity:
    "sum ?g Omega / exp (lambda * u) =
      exp (-lambda * u) * sum ?g Omega"
  proof -
    have "sum ?g Omega / exp (lambda * u) =
        inverse (exp (lambda * u)) * sum ?g Omega"
      unfolding field_class.field_divide_inverse by (rule mult.commute)
    also have "... = exp (-lambda * u) * sum ?g Omega"
      using exp_inverse by (simp only: exp_inverse)
    finally show ?thesis .
  qed
  have card_bound':
    "real (card ?A) \<le> exp (-lambda * u) * sum ?g Omega"
  proof -
    note card_bound
    also note quotient_identity
    finally show ?thesis .
  qed
  have card_Omega_pos: "0 < card Omega"
    using finite_Omega nonempty_Omega by (simp add: card_gt_0_iff)
  have denominator_pos: "0 < real (card Omega)"
    using card_Omega_pos by simp
  have "real (card ?A) / real (card Omega) \<le>
      (exp (-lambda * u) * sum ?g Omega) / real (card Omega)"
    using card_bound' less_imp_le[OF denominator_pos]
    by (rule divide_right_mono)  also have "... = exp (-lambda * u) *
      (sum ?g Omega / real (card Omega))"
    by simp
  finally show ?thesis
    unfolding uniform_probability_def uniform_expectation_def .
qed

lemma uniform_probability_le_one:
  assumes finite_Omega: "finite Omega"
  shows "uniform_probability Omega E \<le> 1"
proof -
  have card_bound: "card (Omega \<inter> E) \<le> card Omega"
    using finite_Omega by (intro card_mono) auto
  show ?thesis
  proof (cases "card Omega = 0")
    case True
    then show ?thesis
      unfolding uniform_probability_def by simp
  next
    case False
    have denominator_pos: "0 < real (card Omega)"
      using False by simp
    have "real (card (Omega \<inter> E)) / real (card Omega) \<le>
        real (card Omega) / real (card Omega)"
      using card_bound less_imp_le[OF denominator_pos]
      by (intro divide_right_mono) simp_all
    also have "... = 1"
      using False by simp
    finally show ?thesis
      unfolding uniform_probability_def .
  qed
qed

lemma uniform_subset_upper_tail:
  fixes u :: real
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and finite_K: "finite K"
    and K_subset: "K \<subseteq> U"
    and nonempty_K: "0 < card K"
    and u_nonneg: "0 \<le> u"
  shows "uniform_probability (k_subsets U n)
      {S. u \<le> real (subset_count K S) -
        real (card K) * (real n / real (card U))} \<le>
    exp (-2 * u\<^sup>2 / real (card K))"
proof -
  let ?Omega = "k_subsets U n"
  let ?p = "real n / real (card U)"
  let ?k = "real (card K)"
  have finite_Omega: "finite ?Omega"
    using finite_U by (simp add: k_subsets_def)
  have nonempty_Omega: "?Omega \<noteq> {}"
  proof -
    obtain S where S_subset: "S \<subseteq> U" and card_S: "card S = n"
      using obtain_subset_with_card_n[OF sample_size] by blast
    have "S \<in> ?Omega"
      using S_subset card_S by (simp add: k_subsets_def)
    then show ?thesis by blast
  qed
  show ?thesis
  proof (cases "u = 0")
    case True
    have "uniform_probability ?Omega
        {S. u \<le> real (subset_count K S) - ?k * ?p} \<le> 1"
      by (rule uniform_probability_le_one[OF finite_Omega])
    then show ?thesis
      using True by simp
  next
    case False
    have u_pos: "0 < u"
      using u_nonneg False by simp
    let ?lambda = "4 * u / ?k"
    have k_pos: "0 < ?k"
      using nonempty_K by simp
    have k_nonzero: "?k \<noteq> 0"
      using k_pos by simp
    have lambda_pos: "0 < ?lambda"
      using u_pos k_pos by simp
    have markov_bound:
      "uniform_probability ?Omega
          {S. u \<le> real (subset_count K S) - ?k * ?p} \<le>
       exp (-?lambda * u) *
         uniform_expectation ?Omega
           (\<lambda>S. exp (?lambda *
             (real (subset_count K S) - ?k * ?p)))"
      by (rule uniform_probability_exp_tail[OF finite_Omega nonempty_Omega lambda_pos])
    have moment_bound:
      "uniform_expectation ?Omega
          (\<lambda>S. exp (?lambda *
            (real (subset_count K S) - ?k * ?p))) \<le>
       exp (?k * ?lambda\<^sup>2 / 8)"
      by (rule uniform_subset_centered_exp_moment_bound[OF finite_U nonempty_U
        sample_size finite_K K_subset]) (use lambda_pos in simp)
    have markov_factor_nonneg: "0 \<le> exp (-?lambda * u)" by simp
    have scaled_moment_bound:
      "exp (-?lambda * u) *
         uniform_expectation ?Omega
           (\<lambda>S. exp (?lambda *
             (real (subset_count K S) - ?k * ?p))) \<le>
       exp (-?lambda * u) * exp (?k * ?lambda\<^sup>2 / 8)"
      using moment_bound markov_factor_nonneg by (rule mult_left_mono)
    have exponent_identity:
      "-?lambda * u + ?k * ?lambda\<^sup>2 / 8 =
       -2 * u\<^sup>2 / ?k"
      using k_nonzero by (simp add: power2_eq_square field_simps; algebra)
    have product_identity:
      "exp (-?lambda * u) * exp (?k * ?lambda\<^sup>2 / 8) =
       exp (-2 * u\<^sup>2 / ?k)"
    proof -
      have "exp (-?lambda * u) * exp (?k * ?lambda\<^sup>2 / 8) =
          exp (-?lambda * u + ?k * ?lambda\<^sup>2 / 8)"
        by (simp only: exp_add)
      also have "... = exp (-2 * u\<^sup>2 / ?k)"
        unfolding exponent_identity by simp
      finally show ?thesis .
    qed
    note markov_bound
    also note scaled_moment_bound
    also note product_identity
    finally show ?thesis .
  qed
qed

lemma bij_betw_k_subsets_complement:
  assumes finite_U: "finite U"
    and sample_size: "n \<le> card U"
  shows "bij_betw (\<lambda>S. U - S) (k_subsets U n)
    (k_subsets U (card U - n))"
proof -
  have maps: "U - S \<in> k_subsets U (card U - n)"
    if S: "S \<in> k_subsets U n" for S
  proof -
    have S_subset: "S \<subseteq> U" and card_S: "card S = n"
      using S by (auto simp: k_subsets_def)
    have finite_S: "finite S"
      using finite_U S_subset by (meson finite_subset)
    have card_complement: "card (U - S) = card U - n"
      using card_Diff_subset[OF finite_S S_subset] card_S by simp
    show ?thesis
      using card_complement by (simp add: k_subsets_def)
  qed
  have injective: "inj_on (\<lambda>S. U - S) (k_subsets U n)"
  proof (rule inj_onI)
    fix S T
    assume S: "S \<in> k_subsets U n"
      and T: "T \<in> k_subsets U n"
      and complements: "U - S = U - T"
    have S_subset: "S \<subseteq> U" and T_subset: "T \<subseteq> U"
      using S T by (auto simp: k_subsets_def)
    have "S = U - (U - S)"
      using S_subset by blast
    also have "... = U - (U - T)"
      using complements by simp
    also have "... = T"
      using T_subset by blast
    finally show "S = T" .
  qed
  have image_eq:
    "(\<lambda>S. U - S) ` k_subsets U n =
      k_subsets U (card U - n)"
  proof (rule equalityI)
    show "(\<lambda>S. U - S) ` k_subsets U n \<subseteq>
        k_subsets U (card U - n)"
      using maps by blast
    show "k_subsets U (card U - n) \<subseteq>
        (\<lambda>S. U - S) ` k_subsets U n"
    proof
      fix T
      assume T: "T \<in> k_subsets U (card U - n)"
      have T_subset: "T \<subseteq> U" and card_T: "card T = card U - n"
        using T by (auto simp: k_subsets_def)
      have finite_T: "finite T"
        using finite_U T_subset by (meson finite_subset)
      let ?S = "U - T"
      have card_S: "card ?S = n"
      proof -
        have "card ?S = card U - card T"
          by (rule card_Diff_subset[OF finite_T T_subset])
        also have "... = n"
          using card_T sample_size by simp
        finally show ?thesis .
      qed
      have S_member: "?S \<in> k_subsets U n"
        using card_S by (simp add: k_subsets_def)
      have complement_S: "U - ?S = T"
        using T_subset by blast
      show "T \<in> (\<lambda>S. U - S) ` k_subsets U n"
        using S_member complement_S by blast
    qed
  qed
  show ?thesis
    unfolding bij_betw_def using injective image_eq by blast
qed
lemma uniform_probability_bij_betw:
  assumes finite_Omega: "finite Omega"
    and bijection: "bij_betw f Omega Omega'"
  shows "uniform_probability Omega {x. f x \<in> E} =
    uniform_probability Omega' E"
proof -
  let ?A = "Omega \<inter> {x. f x \<in> E}"
  have inj: "inj_on f Omega"
    using bijection by (rule bij_betw_imp_inj_on)
  have inj_A: "inj_on f ?A"
    using inj by (rule inj_on_subset) simp
  have image_event: "f ` ?A = Omega' \<inter> E"
    using bijection by (auto simp: bij_betw_def)
  have event_card: "card ?A = card (Omega' \<inter> E)"
  proof -
    have "card (f ` ?A) = card ?A"
      using inj_A by (rule card_image)
    then show ?thesis
      unfolding image_event by simp
  qed
  have support_card: "card Omega = card Omega'"
    using bijection by (rule bij_betw_same_card)
  show ?thesis
    unfolding uniform_probability_def
    using event_card support_card by simp
qed

lemma uniform_subset_lower_tail:
  fixes u :: real
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and finite_K: "finite K"
    and K_subset: "K \<subseteq> U"
    and nonempty_K: "0 < card K"
    and u_nonneg: "0 \<le> u"
  shows "uniform_probability (k_subsets U n)
      {S. u \<le> real (card K) * (real n / real (card U)) -
        real (subset_count K S)} \<le>
    exp (-2 * u\<^sup>2 / real (card K))"
proof -
  let ?Omega = "k_subsets U n"
  let ?Omega' = "k_subsets U (card U - n)"
  let ?p = "real n / real (card U)"
  let ?p' = "real (card U - n) / real (card U)"
  let ?k = "real (card K)"
  let ?E = "{T. u \<le> real (subset_count K T) - ?k * ?p'}"
  have finite_Omega: "finite ?Omega"
    using finite_U by (simp add: k_subsets_def)
  have complement_bijection:
    "bij_betw (\<lambda>S. U - S) ?Omega ?Omega'"
    by (rule bij_betw_k_subsets_complement[OF finite_U sample_size])
  have complement_fraction: "?p' = 1 - ?p"
  proof -
    have card_difference:
      "real (card U - n) = real (card U) - real n"
      using sample_size by simp
    have denominator_nonzero: "real (card U) \<noteq> 0"
      using nonempty_U by simp
    show ?thesis
      unfolding card_difference
      using denominator_nonzero by (simp add: diff_divide_distrib)
  qed
  have centered_complement:
    "real (subset_count K (U - S)) - ?k * ?p' =
      ?k * ?p - real (subset_count K S)"
    if S: "S \<in> ?Omega" for S
  proof -
    have S_subset: "S \<subseteq> U"
      using S by (simp add: k_subsets_def)
    have finite_inter: "finite (K \<inter> S)"
      using finite_K by simp
    have count_complement_nat:
      "subset_count K (U - S) = card K - subset_count K S"
    proof -
      have set_identity: "K \<inter> (U - S) = K - S"
        using K_subset by blast
      show ?thesis
        unfolding subset_count_def set_identity
        by (rule card_Diff_subset_Int[OF finite_inter])
    qed
    have count_le: "subset_count K S \<le> card K"
      unfolding subset_count_def
      by (rule card_mono[OF finite_K]) simp
    have count_complement_real:
      "real (subset_count K (U - S)) =
        ?k - real (subset_count K S)"
      unfolding count_complement_nat using count_le by simp
    show ?thesis
      using count_complement_real complement_fraction by algebra
  qed
  have source_event_eq:
    "?Omega \<inter>
        {S. u \<le> ?k * ?p - real (subset_count K S)} =
     ?Omega \<inter> {S. U - S \<in> ?E}"
  proof (rule equalityI)
    show "?Omega \<inter>
        {S. u \<le> ?k * ?p - real (subset_count K S)} \<subseteq>
      ?Omega \<inter> {S. U - S \<in> ?E}"
    proof
      fix S
      assume source: "S \<in> ?Omega \<inter>
        {S. u \<le> ?k * ?p - real (subset_count K S)}"
      have S_Omega: "S \<in> ?Omega" and lower:
        "u \<le> ?k * ?p - real (subset_count K S)"
        using source by auto
      have transformed:
        "u \<le> real (subset_count K (U - S)) - ?k * ?p'"
        using lower by (simp only: centered_complement[OF S_Omega])
      show "S \<in> ?Omega \<inter> {S. U - S \<in> ?E}"
        using S_Omega transformed by simp
    qed
    show "?Omega \<inter> {S. U - S \<in> ?E} \<subseteq>
      ?Omega \<inter>
        {S. u \<le> ?k * ?p - real (subset_count K S)}"
    proof
      fix S
      assume source: "S \<in> ?Omega \<inter> {S. U - S \<in> ?E}"
      have S_Omega: "S \<in> ?Omega" and transformed:
        "u \<le> real (subset_count K (U - S)) - ?k * ?p'"
        using source by auto
      have lower: "u \<le> ?k * ?p - real (subset_count K S)"
        using transformed by (simp only: centered_complement[OF S_Omega])
      show "S \<in> ?Omega \<inter>
          {S. u \<le> ?k * ?p - real (subset_count K S)}"
        using S_Omega lower by simp
    qed
  qed
  have transported_probability:
    "uniform_probability ?Omega {S. U - S \<in> ?E} =
      uniform_probability ?Omega' ?E"
    by (rule uniform_probability_bij_betw[OF finite_Omega complement_bijection])
  have lower_probability_identity:
    "uniform_probability ?Omega
        {S. u \<le> ?k * ?p - real (subset_count K S)} =
      uniform_probability ?Omega' ?E"
  proof -
    have "uniform_probability ?Omega
        {S. u \<le> ?k * ?p - real (subset_count K S)} =
      uniform_probability ?Omega {S. U - S \<in> ?E}"
      unfolding uniform_probability_def
      using source_event_eq by simp
    also note transported_probability
    finally show ?thesis .
  qed
  have complement_sample_size: "card U - n \<le> card U" by simp
  have upper_complement:
    "uniform_probability ?Omega' ?E \<le>
      exp (-2 * u\<^sup>2 / ?k)"
    by (rule uniform_subset_upper_tail[OF finite_U nonempty_U
      complement_sample_size finite_K K_subset nonempty_K u_nonneg])
  note lower_probability_identity
  also note upper_complement
  finally show ?thesis .
qed

lemma uniform_probability_Un_le:
  assumes finite_Omega: "finite Omega"
  shows "uniform_probability Omega (A \<union> B) \<le>
    uniform_probability Omega A + uniform_probability Omega B"
proof -
  have card_union:
    "card (Omega \<inter> (A \<union> B)) \<le>
      card (Omega \<inter> A) + card (Omega \<inter> B)"
    using card_Un_le[of "Omega \<inter> A" "Omega \<inter> B"]
    by (simp add: Int_Un_distrib)
  have denominator_nonneg: "0 \<le> real (card Omega)" by simp
  show ?thesis
    unfolding uniform_probability_def
    unfolding add_divide_distrib[symmetric]
    by (rule divide_right_mono[OF _ denominator_nonneg])
      (use card_union in simp)
qed

lemma uniform_subset_two_sided:
  fixes u :: real
  assumes finite_U: "finite U"
    and nonempty_U: "0 < card U"
    and sample_size: "n \<le> card U"
    and finite_K: "finite K"
    and K_subset: "K \<subseteq> U"
    and nonempty_K: "0 < card K"
    and u_nonneg: "0 \<le> u"
  shows "uniform_probability (k_subsets U n)
      {S. u \<le> \<bar>real (subset_count K S) -
        real (card K) * (real n / real (card U))\<bar>} \<le>
    2 * exp (-2 * u\<^sup>2 / real (card K))"
proof -
  let ?Omega = "k_subsets U n"
  let ?p = "real n / real (card U)"
  let ?k = "real (card K)"
  let ?X = "\<lambda>S. real (subset_count K S) - ?k * ?p"
  let ?Upper = "{S. u \<le> ?X S}"
  let ?Lower = "{S. u \<le> ?k * ?p - real (subset_count K S)}"
  have absolute_event:
    "{S. u \<le> \<bar>?X S\<bar>} = ?Upper \<union> ?Lower"
    using u_nonneg by (auto simp: abs_if)
  have finite_Omega: "finite ?Omega"
    using finite_U by (simp add: k_subsets_def)
  have union_bound:
    "uniform_probability ?Omega (?Upper \<union> ?Lower) \<le>
      uniform_probability ?Omega ?Upper +
      uniform_probability ?Omega ?Lower"
    by (rule uniform_probability_Un_le[OF finite_Omega])
  have upper_bound:
    "uniform_probability ?Omega ?Upper \<le>
      exp (-2 * u\<^sup>2 / ?k)"
    by (rule uniform_subset_upper_tail[OF finite_U nonempty_U
      sample_size finite_K K_subset nonempty_K u_nonneg])
  have lower_bound:
    "uniform_probability ?Omega ?Lower \<le>
      exp (-2 * u\<^sup>2 / ?k)"
    by (fact uniform_subset_lower_tail[OF finite_U nonempty_U
      sample_size finite_K K_subset nonempty_K u_nonneg])
  have "uniform_probability ?Omega {S. u \<le> \<bar>?X S\<bar>} =
      uniform_probability ?Omega (?Upper \<union> ?Lower)"
    by (simp only: absolute_event)
  also have "... \<le> uniform_probability ?Omega ?Upper +
      uniform_probability ?Omega ?Lower"
    by (rule union_bound)
  also have "... \<le> exp (-2 * u\<^sup>2 / ?k) +
      exp (-2 * u\<^sup>2 / ?k)"
    by (rule add_mono[OF upper_bound lower_bound])
  also have "... = 2 * exp (-2 * u\<^sup>2 / ?k)"
    by algebra
  finally show ?thesis .
qed

definition subset_centered_prefix ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> real" where
  "subset_centered_prefix n N S k =
    real (subset_count {..<k} S) - real k * (real n / real N)"

definition subset_max_centered_prefix ::
    "nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> real" where
  "subset_max_centered_prefix n N S =
    Max ((\<lambda>k. abs (subset_centered_prefix n N S k)) ` {1..N})"

lemma uniform_subset_prefix_two_sided:
  fixes u :: real
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and prefix_positive: "0 < k"
    and prefix_size: "k \<le> N"
    and u_nonneg: "0 \<le> u"
  shows "uniform_probability (k_subsets {..<N} n)
      {S. u \<le> \<bar>subset_centered_prefix n N S k\<bar>} \<le>
    2 * exp (-2 * u\<^sup>2 / real k)"
  unfolding subset_centered_prefix_def
  using uniform_subset_two_sided[of "{..<N}" n "{..<k}" u] assms
  by simp

lemma uniform_probability_UNION_le:
  assumes finite_Omega: "finite Omega"
    and finite_I: "finite I"
  shows "uniform_probability Omega (\<Union>i\<in>I. E i) \<le>
    (\<Sum>i\<in>I. uniform_probability Omega (E i))"
  using finite_I
proof (induction rule: finite_induct)
  case empty
  then show ?case by (simp add: uniform_probability_def)
next
  case (insert i I)
  have "uniform_probability Omega
      (E i \<union> (\<Union>j\<in>I. E j)) \<le>
    uniform_probability Omega (E i) +
      uniform_probability Omega (\<Union>j\<in>I. E j)"
    by (rule uniform_probability_Un_le[OF finite_Omega])
  also have "... \<le> uniform_probability Omega (E i) +
      (\<Sum>j\<in>I. uniform_probability Omega (E j))"
    by (rule add_left_mono[OF insert.IH])
  finally show ?case
    using insert.hyps by simp
qed

lemma subset_max_centered_prefix_ge_iff:
  assumes N_positive: "0 < N"
  shows "u \<le> subset_max_centered_prefix n N S \<longleftrightarrow>
    (\<exists>k\<in>{1..N}. u \<le> abs (subset_centered_prefix n N S k))"
  unfolding subset_max_centered_prefix_def
  by (subst Max_ge_iff) (use N_positive in auto)

lemma uniform_subset_max_prefix:
  fixes u :: real
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and u_nonneg: "0 \<le> u"
  shows "uniform_probability (k_subsets {..<N} n)
      {S. u \<le> subset_max_centered_prefix n N S} \<le>
    2 * real N * exp (-2 * u\<^sup>2 / real N)"
proof -
  let ?Omega = "k_subsets {..<N} n"
  let ?I = "{1..N}"
  let ?E = "\<lambda>k. {S. u \<le> abs (subset_centered_prefix n N S k)}"
  let ?B = "2 * exp (-2 * u\<^sup>2 / real N)"
  have finite_Omega: "finite ?Omega"
    by (simp add: k_subsets_def)
  have point_bound: "uniform_probability ?Omega (?E k) \<le> ?B"
    if k_member: "k \<in> ?I" for k
  proof -
    have k_positive: "0 < k" and k_le_N: "k \<le> N"
      using k_member by auto
    have raw_bound:
      "uniform_probability ?Omega (?E k) \<le>
        2 * exp (-2 * u\<^sup>2 / real k)"
      by (rule uniform_subset_prefix_two_sided[OF N_positive
        sample_size k_positive k_le_N u_nonneg])
    have fraction_order:
      "(2 * u\<^sup>2) / real N \<le> (2 * u\<^sup>2) / real k"
      by (rule divide_left_mono)
        (use N_positive k_positive k_le_N in auto)
    have exponent_order:
      "-2 * u\<^sup>2 / real k \<le> -2 * u\<^sup>2 / real N"
      using fraction_order by simp
    have exponential_order:
      "exp (-2 * u\<^sup>2 / real k) \<le>
        exp (-2 * u\<^sup>2 / real N)"
      using exponent_order by simp
    have scaled_bound:
      "2 * exp (-2 * u\<^sup>2 / real k) \<le> ?B"
      by (rule mult_left_mono[OF exponential_order]) simp
    show ?thesis
      by (rule order_trans[OF raw_bound scaled_bound])
  qed
  have maximum_event:
    "{S. u \<le> subset_max_centered_prefix n N S} =
      (\<Union>k\<in>?I. ?E k)"
    using subset_max_centered_prefix_ge_iff[OF N_positive]
    by auto
  have union_bound:
    "uniform_probability ?Omega (\<Union>k\<in>?I. ?E k) \<le>
      (\<Sum>k\<in>?I. uniform_probability ?Omega (?E k))"
    by (rule uniform_probability_UNION_le[OF finite_Omega]) simp
  have sum_bound:
    "(\<Sum>k\<in>?I. uniform_probability ?Omega (?E k)) \<le>
      (\<Sum>k\<in>?I. ?B)"
    by (rule sum_mono) (use point_bound in auto)
  have constant_sum:
    "(\<Sum>k\<in>?I. ?B) =
      2 * real N * exp (-2 * u\<^sup>2 / real N)"
    by simp
  have "uniform_probability ?Omega
      {S. u \<le> subset_max_centered_prefix n N S} =
    uniform_probability ?Omega (\<Union>k\<in>?I. ?E k)"
    by (simp only: maximum_event)
  also note union_bound
  also note sum_bound
  also note constant_sum
  finally show ?thesis .
qed

lemma uniform_subset_max_prefix_confidence:
  fixes delta :: real
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and delta_positive: "0 < delta"
    and delta_at_most_one: "delta \<le> 1"
  defines "u \<equiv> sqrt (real N / 2 * ln (2 * real N / delta))"
  shows "uniform_probability (k_subsets {..<N} n)
      {S. u \<le> subset_max_centered_prefix n N S} \<le> delta"
proof -
  let ?R = "2 * real N / delta"
  let ?A = "real N / 2 * ln ?R"
  have real_N_positive: "0 < real N"
    using N_positive by simp
  have one_le_twice_N: "1 \<le> 2 * real N"
    using N_positive by simp
  have delta_le_twice_N: "delta \<le> 2 * real N"
    using delta_at_most_one one_le_twice_N by (rule order_trans)
  have ratio_positive: "0 < ?R"
    by (rule divide_pos_pos) (use real_N_positive delta_positive in auto)
  have ratio_at_least_one: "1 \<le> ?R"
    using delta_positive delta_le_twice_N
    by (simp add: le_divide_eq)
  have log_nonnegative: "0 \<le> ln ?R"
    using ratio_at_least_one by simp
  have radicand_nonnegative: "0 \<le> ?A"
  proof (rule mult_nonneg_nonneg)
    show "0 \<le> real N / 2"
      using real_N_positive by simp
    show "0 \<le> ln ?R"
      by (rule log_nonnegative)
  qed
  have u_nonnegative: "0 \<le> u"
    unfolding u_def
    by (rule real_sqrt_ge_zero[OF radicand_nonnegative])
  have maximal_bound:
    "uniform_probability (k_subsets {..<N} n)
        {S. u \<le> subset_max_centered_prefix n N S} \<le>
      2 * real N * exp (-2 * u\<^sup>2 / real N)"
    by (rule uniform_subset_max_prefix[OF N_positive sample_size u_nonnegative])
  have u_square: "u\<^sup>2 = ?A"
    unfolding u_def
    by (rule real_sqrt_pow2[OF radicand_nonnegative])
  have exponent_identity:
    "-2 * u\<^sup>2 / real N = - ln ?R"
    using u_square real_N_positive
    by (simp add: divide_simps) algebra
  have exponential_identity: "exp (- ln ?R) = 1 / ?R"
    using ratio_positive by (simp add: exp_minus)
  have final_expression:
    "2 * real N * exp (-2 * u\<^sup>2 / real N) = delta"
  proof -
    have "2 * real N * exp (-2 * u\<^sup>2 / real N) =
        2 * real N * exp (- ln ?R)"
      by (simp only: exponent_identity)
    also have "... = 2 * real N * (1 / ?R)"
      by (simp only: exponential_identity)
    also have "... = delta"
      using real_N_positive delta_positive by (simp add: divide_simps)
    finally show ?thesis .
  qed
  note maximal_bound
  also note final_expression
  finally show ?thesis .
qed

section \<open>Uniform binary permutation orders\<close>

definition binary_orders :: "nat \<Rightarrow> nat \<Rightarrow> bool list set" where
  "binary_orders n N = permutations_of_multiset
    (replicate_mset n True + replicate_mset (N - n) False)"

definition true_positions :: "bool list \<Rightarrow> nat set" where
  "true_positions xs = {i. i < length xs \<and> xs ! i}"

lemma count_false_bool:
  "count_list xs False = length xs - count_list xs True"
    proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    have count_le: "count_list xs True \<le> length xs"
      by (rule count_le_length)
    show ?case
      using Cons.IH count_le
      by (cases a) (simp_all add: Suc_diff_le)
  qed

lemma binary_orders_iff:
  assumes sample_size: "n \<le> N"
  shows "xs \<in> binary_orders n N \<longleftrightarrow>
    length xs = N \<and> count_list xs True = n"
proof
  assume xs: "xs \<in> binary_orders n N"
  have multiset:
    "mset xs = replicate_mset n True + replicate_mset (N - n) False"
    using xs by (simp add: binary_orders_def permutations_of_multiset_def)
  have length_xs: "length xs = N"
  proof -
    have "length xs = size (mset xs)" by simp
    also have "... = size
        (replicate_mset n True + replicate_mset (N - n) False)"
      by (simp only: multiset)
    also have "... = N"
      using sample_size by simp
    finally show ?thesis .
  qed
  have true_count: "count_list xs True = n"
    using arg_cong[OF multiset, of "\<lambda>M. count M True"] by (simp add: count_mset)
  show "length xs = N \<and> count_list xs True = n"
    using length_xs true_count by simp
next
  assume xs: "length xs = N \<and> count_list xs True = n"
  have length_xs: "length xs = N" and true_count: "count_list xs True = n"
    using xs by auto
  have multiset:
    "mset xs = replicate_mset n True + replicate_mset (N - n) False"
  proof (rule multiset_eqI)
    fix b
    show "count (mset xs) b =
      count (replicate_mset n True + replicate_mset (N - n) False) b"
    proof (cases b)
      case False
      then show ?thesis
        using length_xs true_count sample_size
        by (simp add: count_false_bool count_mset)
    next
      case True
      then show ?thesis
        using true_count by (simp add: count_mset)
    qed
  qed
  show "xs \<in> binary_orders n N"
    using multiset by (simp add: binary_orders_def permutations_of_multiset_def)
qed

lemma card_true_positions:
  "card (true_positions xs) = count_list xs True"
  unfolding true_positions_def count_list_eq_length_filter
  using length_filter_conv_card[of "(=) True" xs]
  by simp

lemma bool_list_from_true_positions:
  assumes length_xs: "length xs = N"
  shows "map (\<lambda>i. i \<in> true_positions xs) [0..<N] = xs"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. i \<in> true_positions xs) [0..<N]) =
    length xs"
    using length_xs by simp
  fix i
  assume i: "i < length (map (\<lambda>i. i \<in> true_positions xs) [0..<N])"
  have i_N: "i < N" using i by simp
  show "map (\<lambda>i. i \<in> true_positions xs) [0..<N] ! i = xs ! i"
    using i_N length_xs
    by (cases "xs ! i") (simp_all add: true_positions_def nth_map_upt)
qed

lemma true_positions_canonical:
  assumes S_subset: "S \<subseteq> {..<N}"
  shows "true_positions (map (\<lambda>i. i \<in> S) [0..<N]) = S"
  unfolding true_positions_def
  using S_subset
  by (auto simp: nth_map_upt)

lemma true_positions_bij_betw:
  assumes sample_size: "n \<le> N"
  shows "bij_betw true_positions (binary_orders n N)
    (k_subsets {..<N} n)"
proof -
  have maps: "true_positions xs \<in> k_subsets {..<N} n"
    if xs: "xs \<in> binary_orders n N" for xs
  proof -
    have length_xs: "length xs = N" and count_xs: "count_list xs True = n"
      using xs binary_orders_iff[OF sample_size] by auto
    have subset: "true_positions xs \<subseteq> {..<N}"
      using length_xs by (auto simp: true_positions_def)
    have card: "card (true_positions xs) = n"
      using card_true_positions count_xs by simp
    show ?thesis
      using subset card by (simp add: k_subsets_def)
  qed
  have injective: "inj_on true_positions (binary_orders n N)"
  proof (rule inj_onI)
    fix xs ys
    assume xs: "xs \<in> binary_orders n N"
      and ys: "ys \<in> binary_orders n N"
      and positions: "true_positions xs = true_positions ys"
    have length_xs: "length xs = N" and length_ys: "length ys = N"
      using xs ys binary_orders_iff[OF sample_size] by auto
    have "xs = map (\<lambda>i. i \<in> true_positions xs) [0..<N]"
      using bool_list_from_true_positions[OF length_xs] by simp
    also have "... = map (\<lambda>i. i \<in> true_positions ys) [0..<N]"
      using positions by simp
    also have "... = ys"
      by (rule bool_list_from_true_positions[OF length_ys])
    finally show "xs = ys" .
  qed
  have image_eq:
    "true_positions ` binary_orders n N = k_subsets {..<N} n"
  proof (rule equalityI)
    show "true_positions ` binary_orders n N \<subseteq> k_subsets {..<N} n"
      using maps by blast
    show "k_subsets {..<N} n \<subseteq> true_positions ` binary_orders n N"
    proof
      fix S
      assume S: "S \<in> k_subsets {..<N} n"
      have S_subset: "S \<subseteq> {..<N}" and card_S: "card S = n"
        using S by (auto simp: k_subsets_def)
      let ?xs = "map (\<lambda>i. i \<in> S) [0..<N]"
      have positions: "true_positions ?xs = S"
        by (rule true_positions_canonical[OF S_subset])
      have length_xs: "length ?xs = N" by simp
      have count_xs: "count_list ?xs True = n"
        using card_true_positions[of ?xs] positions card_S by simp
      have xs_member: "?xs \<in> binary_orders n N"
        using binary_orders_iff[OF sample_size] length_xs count_xs by simp
      show "S \<in> true_positions ` binary_orders n N"
        using xs_member positions by blast
    qed
  qed
  show ?thesis
    unfolding bij_betw_def using injective image_eq by blast
qed

lemma uniform_binary_order_probability:
  assumes sample_size: "n \<le> N"
  shows "uniform_probability (binary_orders n N)
      {xs. true_positions xs \<in> E} =
    uniform_probability (k_subsets {..<N} n) E"
  by (rule uniform_probability_bij_betw)
    (simp add: binary_orders_def,
     rule true_positions_bij_betw[OF sample_size])

definition binary_centered_prefix ::
    "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "binary_centered_prefix n N xs k =
    subset_centered_prefix n N (true_positions xs) k"

definition binary_max_centered_prefix ::
    "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> real" where
  "binary_max_centered_prefix n N xs =
    subset_max_centered_prefix n N (true_positions xs)"

lemma uniform_binary_order_max_prefix_confidence:
  fixes delta :: real
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and delta_positive: "0 < delta"
    and delta_at_most_one: "delta \<le> 1"
  defines "u \<equiv> sqrt (real N / 2 * ln (2 * real N / delta))"
  shows "uniform_probability (binary_orders n N)
      {xs. u \<le> binary_max_centered_prefix n N xs} \<le> delta"
proof -
  have transport:
    "uniform_probability (binary_orders n N)
        {xs. true_positions xs \<in>
          {S. u \<le> subset_max_centered_prefix n N S}} =
      uniform_probability (k_subsets {..<N} n)
        {S. u \<le> subset_max_centered_prefix n N S}"
    by (rule uniform_binary_order_probability[OF sample_size])
  have subset_bound:
    "uniform_probability (k_subsets {..<N} n)
        {S. u \<le> subset_max_centered_prefix n N S} \<le> delta"
    unfolding u_def
    by (rule uniform_subset_max_prefix_confidence[OF N_positive sample_size
      delta_positive delta_at_most_one])
  have "uniform_probability (binary_orders n N)
      {xs. u \<le> binary_max_centered_prefix n N xs} =
    uniform_probability (k_subsets {..<N} n)
      {S. u \<le> subset_max_centered_prefix n N S}"
    unfolding binary_max_centered_prefix_def
    using transport by simp


  also note subset_bound
  finally show ?thesis .
qed
lemma sigmoid_has_real_derivative:
  "(sigmoid has_real_derivative
    (exp (- x) / (1 + exp (- x))^2)) (at x)"
proof -
  have denominator: "1 + exp (-x) \<noteq> 0"
    using exp_gt_zero[of "-x"] by linarith
  show ?thesis
    unfolding sigmoid_def
    by (rule derivative_eq_intros | simp add: power2_eq_square denominator field_simps)+
qed

lemma sigmoid_derivative_bounds:
  fixes x :: real
  shows "0 \<le> exp (- x) / (1 + exp (- x))^2"
    and "exp (- x) / (1 + exp (- x))^2 \<le> 1 / 4"
proof -
  have e_pos: "0 < exp (-x)"
    by (rule exp_gt_zero)
  have denominator_pos: "0 < 1 + exp (-x)"
    using e_pos by linarith
  have denominator_square_pos: "0 < (1 + exp (-x))^2"
    unfolding power2_eq_square
    by (rule mult_pos_pos[OF denominator_pos denominator_pos])
  show "0 \<le> exp (- x) / (1 + exp (- x))^2"
    by (rule divide_nonneg_nonneg)
      (use e_pos denominator_square_pos in linarith)+
  have square: "0 \<le> (1 - exp (-x))^2"
    by (rule zero_le_power2)
  have identity:
    "(1 + exp (-x))^2 - 4 * exp (-x) = (1 - exp (-x))^2"
    unfolding power2_eq_square by algebra
  have four: "4 * exp (-x) \<le> (1 + exp (-x))^2"
    using square identity by linarith
  have denominator_square_nonzero: "(1 + exp (-x))^2 \<noteq> 0"
    using denominator_square_pos by linarith
  have positive_scaler: "0 \<le> 4 * (1 + exp (-x))^2"
    using denominator_square_pos by simp
  have scaled:
    "(4 * exp (-x)) / (4 * (1 + exp (-x))^2) \<le>
      (1 + exp (-x))^2 / (4 * (1 + exp (-x))^2)"
    by (rule divide_right_mono[OF four positive_scaler])
  show "exp (- x) / (1 + exp (- x))^2 \<le> 1 / 4"
    using scaled denominator_square_nonzero by (simp add: field_simps)
qed

lemma sigmoid_difference_bounds:
  fixes x y :: real
  assumes xy: "x \<le> y"
  shows "0 \<le> sigmoid y - sigmoid x"
    and "sigmoid y - sigmoid x \<le> (y - x) / 4"
proof -
  have bounds:
    "0 \<le> sigmoid y - sigmoid x \<and>
      sigmoid y - sigmoid x \<le> (y - x) / 4"
  proof (cases "x = y")
    case True
    then show ?thesis by simp
  next
    case False
    have xy_strict: "x < y" using xy False by linarith
    have exists_z:
      "\<exists>z. z > x \<and> z < y \<and>
        sigmoid y - sigmoid x =
          (y - x) * (exp (-z) / (1 + exp (-z))^2)"
      using xy_strict
      by (intro MVT2) (auto intro!: sigmoid_has_real_derivative)
    then obtain z where difference:
      "sigmoid y - sigmoid x =
        (y - x) * (exp (-z) / (1 + exp (-z))^2)"
      by blast
    have gap_nonnegative: "0 \<le> y - x" using xy by linarith
    have derivative_nonnegative:
      "0 \<le> exp (-z) / (1 + exp (-z))^2"
      by (rule sigmoid_derivative_bounds(1))
    have derivative_at_most_quarter:
      "exp (-z) / (1 + exp (-z))^2 \<le> 1 / 4"
      by (rule sigmoid_derivative_bounds(2))
    have nonnegative: "0 \<le> sigmoid y - sigmoid x"
      unfolding difference
      by (rule mult_nonneg_nonneg[OF gap_nonnegative derivative_nonnegative])
    have upper: "sigmoid y - sigmoid x \<le> (y - x) / 4"
    proof -
      have scaled:
        "(y - x) * (exp (-z) / (1 + exp (-z))^2) \<le>
          (y - x) * (1 / 4)"
        by (rule mult_left_mono[OF derivative_at_most_quarter gap_nonnegative])
      show ?thesis
        unfolding difference using scaled
        by (simp only: field_class.field_divide_inverse)

    qed
    show ?thesis using nonnegative upper by blast
  qed
  show "0 \<le> sigmoid y - sigmoid x" using bounds by blast
  show "sigmoid y - sigmoid x \<le> (y - x) / 4" using bounds by blast
qed


definition mean_logistic_step :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "mean_logistic_step eta q w = w + eta * (q - sigmoid w)"

lemma mean_logistic_step_difference_bounds:
  fixes eta q x y :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and xy: "x \<le> y"
  shows "0 \<le> mean_logistic_step eta q y - mean_logistic_step eta q x"
    and "mean_logistic_step eta q y - mean_logistic_step eta q x \<le> y - x"
proof -
  have sigmoid_nonnegative: "0 \<le> sigmoid y - sigmoid x"
    by (rule sigmoid_difference_bounds(1)[OF xy])
  have sigmoid_upper: "sigmoid y - sigmoid x \<le> (y - x) / 4"
    by (rule sigmoid_difference_bounds(2)[OF xy])
  have scaled_nonnegative: "0 \<le> eta * (sigmoid y - sigmoid x)"
    by (rule mult_nonneg_nonneg[OF eta_nonnegative sigmoid_nonnegative])
  have eta_scale:
    "eta * (sigmoid y - sigmoid x) \<le> 4 * (sigmoid y - sigmoid x)"
    by (rule mult_right_mono[OF eta_at_most_four sigmoid_nonnegative])
  have four_scale: "4 * (sigmoid y - sigmoid x) \<le> y - x"
    using mult_left_mono[OF sigmoid_upper, of 4] by simp
  have scaled_upper: "eta * (sigmoid y - sigmoid x) \<le> y - x"
    by (rule order_trans[OF eta_scale four_scale])
  have difference_identity:
    "mean_logistic_step eta q y - mean_logistic_step eta q x =
      (y - x) - eta * (sigmoid y - sigmoid x)"
    unfolding mean_logistic_step_def by algebra
  show "0 \<le> mean_logistic_step eta q y - mean_logistic_step eta q x"
    unfolding difference_identity using scaled_upper by linarith
  show "mean_logistic_step eta q y - mean_logistic_step eta q x \<le> y - x"
    unfolding difference_identity using scaled_nonnegative by linarith
qed

lemma mean_logistic_step_displacement:
  fixes eta q e y :: real
  assumes eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "min e 0 \<le>
      mean_logistic_step eta q (y + e) - mean_logistic_step eta q y \<and>
    mean_logistic_step eta q (y + e) - mean_logistic_step eta q y
      \<le> max e 0"
proof (cases "0 \<le> e")
  case True
  have xy: "y \<le> y + e" using True by linarith
  note pair = mean_logistic_step_difference_bounds[OF eta_nonnegative
    eta_at_most_four xy, of q]
  have nonnegative:
    "0 \<le> mean_logistic_step eta q (y + e) - mean_logistic_step eta q y"
    by (rule pair(1))
  have upper:
    "mean_logistic_step eta q (y + e) - mean_logistic_step eta q y \<le> e"
    using pair(2) by simp
  show ?thesis using True nonnegative upper by simp
next
  case False
  have xy: "y + e \<le> y" using False by linarith
  note pair = mean_logistic_step_difference_bounds[OF eta_nonnegative
    eta_at_most_four xy, of q]
  have nonpositive:
    "mean_logistic_step eta q (y + e) - mean_logistic_step eta q y \<le> 0"
    using pair(1) by linarith
  have lower:
    "e \<le> mean_logistic_step eta q (y + e) - mean_logistic_step eta q y"
    using pair(2) by linarith
  show ?thesis using False nonpositive lower by simp
qed


definition prefix_sum :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "prefix_sum d k = (\<Sum>i<k. d i)"

primrec perturbed_iteration ::
    "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow>
      real \<Rightarrow> nat \<Rightarrow> real" where
  "perturbed_iteration F eta d x 0 = x"
| "perturbed_iteration F eta d x (Suc k) =
    F (perturbed_iteration F eta d x k) + eta * d k"

lemma prefix_sum_Suc [simp]:
  "prefix_sum d (Suc k) = prefix_sum d k + d k"
  unfolding prefix_sum_def by simp

lemma prefix_controlled_perturbation:
  fixes F :: "real \<Rightarrow> real"
    and eta M :: real
    and d :: "nat \<Rightarrow> real"
  assumes eta_nonnegative: "0 \<le> eta"
    and displacement: "\<And>y e. min e 0 \<le> F (y + e) - F y \<and>
      F (y + e) - F y \<le> max e 0"
    and prefix_bound: "\<And>j. j \<le> K \<Longrightarrow> abs (prefix_sum d j) \<le> M"
    and total_zero: "prefix_sum d K = 0"
  shows "abs (perturbed_iteration F eta d x K - (F ^^ K) x) \<le> eta * M"
proof -
  have invariant:
    "eta * (prefix_sum d k - M) \<le>
        perturbed_iteration F eta d x k - (F ^^ k) x \<and>
      perturbed_iteration F eta d x k - (F ^^ k) x \<le>
        eta * (prefix_sum d k + M)"
    if k_le: "k \<le> K" for k
    using k_le
  proof (induction k)
    case 0
    have M_nonnegative: "0 \<le> M"
      using prefix_bound[of 0] by (simp add: prefix_sum_def)
    have eta_M_nonnegative: "0 \<le> eta * M"
      by (rule mult_nonneg_nonneg[OF eta_nonnegative M_nonnegative])
    show ?case
      using eta_M_nonnegative by (simp add: prefix_sum_def)
  next
    case (Suc k)
    have k_le: "k \<le> K" using Suc.prems by simp
    have ih_lower:
      "eta * (prefix_sum d k - M) \<le>
        perturbed_iteration F eta d x k - (F ^^ k) x"
      and ih_upper:
      "perturbed_iteration F eta d x k - (F ^^ k) x \<le>
        eta * (prefix_sum d k + M)"
      using Suc.IH[OF k_le] by auto
    let ?e = "perturbed_iteration F eta d x k - (F ^^ k) x"
    let ?y = "(F ^^ k) x"
    have actual_identity:
      "perturbed_iteration F eta d x k = ?y + ?e" by simp
    have step_displacement:
      "min ?e 0 \<le> F (?y + ?e) - F ?y \<and>
        F (?y + ?e) - F ?y \<le> max ?e 0"
      by (rule displacement)
    have old_prefix_upper: "prefix_sum d k \<le> M"
      using prefix_bound[OF k_le] by linarith
    have old_prefix_lower: "-M \<le> prefix_sum d k"
      using prefix_bound[OF k_le] by linarith
    have prefix_difference_nonpositive: "prefix_sum d k - M \<le> 0"
      using old_prefix_upper by linarith
    have lower_barrier_nonpositive:
      "eta * (prefix_sum d k - M) \<le> 0"
      by (rule mult_nonneg_nonpos[OF eta_nonnegative prefix_difference_nonpositive])
    have prefix_sum_nonnegative: "0 \<le> prefix_sum d k + M"
      using old_prefix_lower by linarith
    have upper_barrier_nonnegative:
      "0 \<le> eta * (prefix_sum d k + M)"
      by (rule mult_nonneg_nonneg[OF eta_nonnegative prefix_sum_nonnegative])
    have lower_min:
      "eta * (prefix_sum d k - M) \<le> min ?e 0"
      using ih_lower lower_barrier_nonpositive by simp
    have displacement_lower:
      "eta * (prefix_sum d k - M) \<le> F (?y + ?e) - F ?y"
      by (rule order_trans[OF lower_min step_displacement[THEN conjunct1]])
    have max_upper:
      "max ?e 0 \<le> eta * (prefix_sum d k + M)"
      using ih_upper upper_barrier_nonnegative by simp
    have displacement_upper:
      "F (?y + ?e) - F ?y \<le> eta * (prefix_sum d k + M)"
      by (rule order_trans[OF step_displacement[THEN conjunct2] max_upper])
    have next_error:
      "perturbed_iteration F eta d x (Suc k) - (F ^^ Suc k) x =
        (F (?y + ?e) - F ?y) + eta * d k"
    proof -
      have "perturbed_iteration F eta d x (Suc k) - (F ^^ Suc k) x =
          F (perturbed_iteration F eta d x k) + eta * d k - F ?y"
        by (simp add: funpow_Suc_right)
      also have "... = (F (?y + ?e) - F ?y) + eta * d k"
        using actual_identity by simp
      finally show ?thesis .
    qed
    have lower_identity:
      "eta * (prefix_sum d (Suc k) - M) =
        eta * (prefix_sum d k - M) + eta * d k"
      by (simp add: algebra_simps)
    have upper_identity:
      "eta * (prefix_sum d (Suc k) + M) =
        eta * (prefix_sum d k + M) + eta * d k"
      by (simp add: algebra_simps)
    show ?case
      unfolding next_error lower_identity upper_identity
      using displacement_lower displacement_upper by linarith
  qed
  have final_bounds:
    "- eta * M \<le> perturbed_iteration F eta d x K - (F ^^ K) x \<and>
      perturbed_iteration F eta d x K - (F ^^ K) x \<le> eta * M"
    using invariant[of K] total_zero by simp
  show ?thesis
    using final_bounds by (simp add: abs_le_iff)
qed

definition bool_value :: "bool \<Rightarrow> real" where
  "bool_value b = (if b then 1 else 0)"

definition binary_innovation :: "real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "binary_innovation q xs i = bool_value (xs ! i) - q"

definition binary_logistic_state ::
    "real \<Rightarrow> real \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> real" where
  "binary_logistic_state eta q xs k =
    perturbed_iteration (mean_logistic_step eta q) eta
      (binary_innovation q xs) 0 k"

definition mean_logistic_state :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "mean_logistic_state eta q k = ((mean_logistic_step eta q) ^^ k) 0"

lemma binary_logistic_state_Suc:
  "binary_logistic_state eta q xs (Suc k) =
    binary_logistic_state eta q xs k +
      eta * (bool_value (xs ! k) - sigmoid (binary_logistic_state eta q xs k))"
  unfolding binary_logistic_state_def binary_innovation_def
    mean_logistic_step_def
  by (simp add: algebra_simps)

lemma prefix_sum_binary_innovation:
  assumes prefix_size: "k \<le> length xs"
  shows "prefix_sum (binary_innovation q xs) k =
    real (subset_count {..<k} (true_positions xs)) - real k * q"
  using prefix_size
proof (induction k)
  case 0
  then show ?case by (simp add: prefix_sum_def subset_count_def)
next
  case (Suc k)
  have k_length: "k < length xs" using Suc.prems by simp
  have count_Suc:
    "subset_count {..<Suc k} (true_positions xs) =
      subset_count {..<k} (true_positions xs) + (if xs ! k then 1 else 0)"
    unfolding subset_count_def true_positions_def
    using k_length by (simp add: lessThan_Suc)
  have ih:
    "prefix_sum (binary_innovation q xs) k =
      real (subset_count {..<k} (true_positions xs)) - real k * q"
    by (rule Suc.IH) (use Suc.prems in simp)
  have innovation:
    "binary_innovation q xs k = (if xs ! k then 1 else 0) - q"
    by (simp add: binary_innovation_def bool_value_def)
  have cast_count:
    "real (subset_count {..<Suc k} (true_positions xs)) =
      real (subset_count {..<k} (true_positions xs)) +
        (if xs ! k then 1 else 0)"
    using count_Suc by (cases "xs ! k") simp_all
  have "prefix_sum (binary_innovation q xs) (Suc k) =
      prefix_sum (binary_innovation q xs) k + binary_innovation q xs k"
    by simp
  also have "... =
      (real (subset_count {..<k} (true_positions xs)) - real k * q) +
        ((if xs ! k then 1 else 0) - q)"
    using ih innovation by simp
  also have "... =
      real (subset_count {..<Suc k} (true_positions xs)) - real (Suc k) * q"
    using cast_count by (cases "xs ! k") (simp_all add: algebra_simps)
  finally show ?case .
qed


lemma subset_centered_prefix_le_max:
  assumes N_positive: "0 < N"
    and k_positive: "0 < k"
    and k_le_N: "k \<le> N"
  shows "abs (subset_centered_prefix n N S k) \<le>
    subset_max_centered_prefix n N S"
  unfolding subset_max_centered_prefix_def
  by (rule Max_ge) (use k_positive k_le_N in auto)

lemma prefix_sum_binary_centered:
  assumes xs_order: "xs \<in> binary_orders n N"
    and sample_size: "n \<le> N"
    and k_le_N: "k \<le> N"
  shows "prefix_sum (binary_innovation (real n / real N) xs) k =
    subset_centered_prefix n N (true_positions xs) k"
proof -
  have length_xs: "length xs = N"
    using xs_order binary_orders_iff[OF sample_size] by blast
  show ?thesis
    unfolding subset_centered_prefix_def
    using prefix_sum_binary_innovation[of k xs "real n / real N"]
      k_le_N length_xs by simp
qed

lemma binary_innovation_prefix_le_max:
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and xs_order: "xs \<in> binary_orders n N"
    and k_le_N: "k \<le> N"
  shows "abs (prefix_sum (binary_innovation (real n / real N) xs) k) \<le>
    binary_max_centered_prefix n N xs"
proof (cases k)
  case 0
  have max_nonnegative: "0 \<le> binary_max_centered_prefix n N xs"
  proof -
    let ?A = "image (\<lambda>j. abs (subset_centered_prefix n N
      (true_positions xs) j)) {1..N}"
    have finite_A: "finite ?A" by simp
    have one_member: "1 \<in> {1..N}" using N_positive by simp
    have selected:
      "abs (subset_centered_prefix n N (true_positions xs) 1) \<in> ?A"
      using one_member by blast
    have max_selected:
      "abs (subset_centered_prefix n N (true_positions xs) 1) \<le> Max ?A"
      by (rule Max_ge[OF finite_A selected])
    have "0 \<le> Max ?A"
      using abs_ge_zero[of "subset_centered_prefix n N (true_positions xs) 1"]
        max_selected by linarith
    then show ?thesis
      unfolding binary_max_centered_prefix_def subset_max_centered_prefix_def .
  qed
  show ?thesis using max_nonnegative by (simp add: 0 prefix_sum_def)
next
  case (Suc j)
  have k_positive: "0 < k" using Suc by simp
  have prefix_eq:
    "prefix_sum (binary_innovation (real n / real N) xs) k =
      subset_centered_prefix n N (true_positions xs) k"
    by (rule prefix_sum_binary_centered[OF xs_order sample_size k_le_N])
  have centered_bound:
    "abs (subset_centered_prefix n N (true_positions xs) k) \<le>
      subset_max_centered_prefix n N (true_positions xs)"
    by (rule subset_centered_prefix_le_max[OF N_positive k_positive k_le_N])
  show ?thesis
    unfolding prefix_eq binary_max_centered_prefix_def by (rule centered_bound)
qed

lemma binary_innovation_total_zero:
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and xs_order: "xs \<in> binary_orders n N"
  shows "prefix_sum (binary_innovation (real n / real N) xs) N = 0"
proof -
  have length_xs: "length xs = N" and true_count: "count_list xs True = n"
    using xs_order binary_orders_iff[OF sample_size] by auto
  have position_count: "card (true_positions xs) = n"
    using card_true_positions true_count by simp
  have subset_count_full:
    "subset_count {..<N} (true_positions xs) = n"
  proof -
    have positions_subset: "true_positions xs \<subseteq> {..<N}"
      using length_xs by (auto simp: true_positions_def)
    show ?thesis
      unfolding subset_count_def
      using positions_subset position_count by (simp add: inf.absorb2)
  qed
  have prefix_eq:
    "prefix_sum (binary_innovation (real n / real N) xs) N =
      real n - real N * (real n / real N)"
    using prefix_sum_binary_innovation[of N xs "real n / real N"]
      length_xs subset_count_full by simp
  show ?thesis
    using N_positive prefix_eq by simp
qed

lemma binary_logistic_mean_comparison:
  assumes N_positive: "0 < N"
    and sample_size: "n \<le> N"
    and xs_order: "xs \<in> binary_orders n N"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "abs (binary_logistic_state eta (real n / real N) xs N -
      mean_logistic_state eta (real n / real N) N) \<le>
    eta * binary_max_centered_prefix n N xs"
proof -
  have displacement:
    "min e 0 \<le> mean_logistic_step eta (real n / real N) (y + e) -
        mean_logistic_step eta (real n / real N) y \<and>
      mean_logistic_step eta (real n / real N) (y + e) -
        mean_logistic_step eta (real n / real N) y \<le> max e 0"
    for y e
    by (rule mean_logistic_step_displacement[OF eta_nonnegative eta_at_most_four])
  have prefix_bound:
    "abs (prefix_sum (binary_innovation (real n / real N) xs) j) \<le>
      binary_max_centered_prefix n N xs"
    if "j \<le> N" for j
    by (rule binary_innovation_prefix_le_max[OF N_positive sample_size
      xs_order that])
  have total_zero:
    "prefix_sum (binary_innovation (real n / real N) xs) N = 0"
    by (rule binary_innovation_total_zero[OF N_positive sample_size xs_order])
  show ?thesis
    unfolding binary_logistic_state_def mean_logistic_state_def
    by (rule prefix_controlled_perturbation[OF eta_nonnegative displacement
      prefix_bound total_zero])
qed

lemma sigmoid_zero [simp]: "sigmoid 0 = 1 / 2"
  unfolding sigmoid_def by simp

lemma sigmoid_log_odds:
  fixes p q :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
  shows "sigmoid (ln (q / p)) = q"
proof -
  have ratio_positive: "0 < q / p"
    by (rule divide_pos_pos[OF q_positive p_positive])
  have exponential: "exp (- ln (q / p)) = p / q"
    using ratio_positive p_positive q_positive
    by (simp add: exp_minus divide_inverse)
  show ?thesis
    unfolding sigmoid_def exponential
    using p_positive q_positive total by (simp add: field_simps)
qed

lemma log_odds_positive:
  fixes p q :: real
  assumes p_positive: "0 < p"
    and p_less_q: "p < q"
  shows "0 < ln (q / p)"
proof -
  have "1 < q / p"
    using p_positive p_less_q by (simp add: pos_less_divide_eq)

  then show ?thesis by simp
qed

lemma sigmoid_derivative_identity:
  fixes z :: real
  shows "exp (-z) / (1 + exp (-z))^2 =
    sigmoid z * (1 - sigmoid z)"
proof -
  have denominator: "1 + exp (-z) \<noteq> 0"
    using exp_gt_zero[of "-z"] by linarith
  show ?thesis
    unfolding sigmoid_def power2_eq_square
    using denominator by (simp add: field_simps)
qed

lemma sigmoid_derivative_lower_on_log_odds:
  fixes p q z :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
    and p_less_q: "p < q"
    and z_nonnegative: "0 \<le> z"
    and z_upper: "z \<le> ln (q / p)"
  shows "p * q \<le> exp (-z) / (1 + exp (-z))^2"
proof -
  have half_le_q: "1 / 2 < q"
    using total p_less_q by linarith
  have p_less_half: "p < 1 / 2"
    using total p_less_q by linarith
  have sigmoid_monotone_from_zero:
    "0 \<le> sigmoid z - sigmoid 0"
    by (rule sigmoid_difference_bounds(1)[where x=0 and y=z, OF z_nonnegative])
  have half_le_sigmoid: "1 / 2 \<le> sigmoid z"
    using sigmoid_monotone_from_zero by simp
  have sigmoid_le_q: "sigmoid z \<le> q"
  proof -
    have monotone:
      "0 \<le> sigmoid (ln (q / p)) - sigmoid z"
      by (rule sigmoid_difference_bounds(1)[OF z_upper])
    show ?thesis
      using monotone sigmoid_log_odds[OF p_positive q_positive total] by linarith
  qed
  have p_le_sigmoid: "p \<le> sigmoid z"
    using p_less_half half_le_sigmoid by linarith
  have product_nonnegative:
    "0 \<le> (q - sigmoid z) * (sigmoid z - p)"
    by (rule mult_nonneg_nonneg) (use sigmoid_le_q p_le_sigmoid in linarith)+
  have identity:
    "sigmoid z * (1 - sigmoid z) - p * q =
      (q - sigmoid z) * (sigmoid z - p)"
    using total by algebra
  have "p * q \<le> sigmoid z * (1 - sigmoid z)"
    using product_nonnegative identity by linarith
  then show ?thesis
    unfolding sigmoid_derivative_identity .
qed

lemma sigmoid_strong_slope_on_log_odds:
  fixes p q x y :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
    and p_less_q: "p < q"
    and x_nonnegative: "0 \<le> x"
    and xy: "x \<le> y"
    and y_upper: "y \<le> ln (q / p)"
  shows "p * q * (y - x) \<le> sigmoid y - sigmoid x"
proof (cases "x = y")
  case True
  then show ?thesis by simp
next
  case False
  have xy_strict: "x < y" using xy False by linarith
  have exists_z:
    "\<exists>z. z > x \<and> z < y \<and>
      sigmoid y - sigmoid x =
        (y - x) * (exp (-z) / (1 + exp (-z))^2)"
    using xy_strict
    by (intro MVT2) (auto intro!: sigmoid_has_real_derivative)
  then obtain z where z_lower: "x < z" and z_upper: "z < y"
    and difference: "sigmoid y - sigmoid x =
      (y - x) * (exp (-z) / (1 + exp (-z))^2)"
    by blast
  have z_nonnegative: "0 \<le> z" using x_nonnegative z_lower by linarith
  have z_log_upper: "z \<le> ln (q / p)" using z_upper y_upper by linarith
  have derivative_lower:
    "p * q \<le> exp (-z) / (1 + exp (-z))^2"
    by (rule sigmoid_derivative_lower_on_log_odds[OF p_positive q_positive
      total p_less_q z_nonnegative z_log_upper])
  have gap_nonnegative: "0 \<le> y - x" using xy by linarith
  have scaled:
    "(y - x) * (p * q) \<le>
      (y - x) * (exp (-z) / (1 + exp (-z))^2)"
    by (rule mult_left_mono[OF derivative_lower gap_nonnegative])
  show ?thesis
    unfolding difference using scaled by (simp add: mult.assoc mult.commute)
qed

lemma four_pq_le_one:
  fixes p q :: real
  assumes total: "p + q = 1"
  shows "4 * p * q \<le> 1"
proof -
  have square: "0 \<le> (q - p)^2" by (rule zero_le_power2)
  have identity: "(p + q)^2 - 4 * p * q = (q - p)^2"
    unfolding power2_eq_square by algebra
  have identity_one: "1 - 4 * p * q = (q - p)^2"
    using identity total by simp
  show ?thesis using square identity_one by linarith
qed

lemma mean_logistic_step_fixed_point:
  fixes eta p q :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
  shows "mean_logistic_step eta q (ln (q / p)) = ln (q / p)"
  unfolding mean_logistic_step_def
  using sigmoid_log_odds[OF p_positive q_positive total] by simp

lemma mean_logistic_state_interval:
  fixes eta p q :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
    and p_less_q: "p < q"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "0 \<le> mean_logistic_state eta q k"
    and "mean_logistic_state eta q k \<le> ln (q / p)"
proof -
  have wstar_positive: "0 < ln (q / p)"
    by (rule log_odds_positive[OF p_positive p_less_q])
  have q_above_half: "1 / 2 < q"
    using total p_less_q by linarith
  have step_zero_nonnegative: "0 \<le> mean_logistic_step eta q 0"
  proof -
    have increment_nonnegative: "0 \<le> eta * (q - 1 / 2)"
      by (rule mult_nonneg_nonneg[OF eta_nonnegative])
        (use q_above_half in linarith)
    show ?thesis
      unfolding mean_logistic_step_def using increment_nonnegative by simp
  qed
  have interval:
    "0 \<le> mean_logistic_state eta q k \<and>
      mean_logistic_state eta q k \<le> ln (q / p)"
  proof (induction k)
    case 0
    show ?case using wstar_positive by (simp add: mean_logistic_state_def)
  next
    case (Suc k)
    let ?w = "mean_logistic_state eta q k"
    have step_recurrence:
      "mean_logistic_state eta q (Suc k) = mean_logistic_step eta q ?w"
      by (simp add: mean_logistic_state_def funpow_Suc_right)
    have lower_monotone:
      "0 \<le> mean_logistic_step eta q ?w - mean_logistic_step eta q 0"
      by (rule mean_logistic_step_difference_bounds(1)[OF eta_nonnegative
        eta_at_most_four Suc.IH[THEN conjunct1]])
    have next_nonnegative: "0 \<le> mean_logistic_step eta q ?w"
      using lower_monotone step_zero_nonnegative by linarith
    have upper_monotone:
      "0 \<le> mean_logistic_step eta q (ln (q / p)) -
        mean_logistic_step eta q ?w"
      by (rule mean_logistic_step_difference_bounds(1)[OF eta_nonnegative
        eta_at_most_four Suc.IH[THEN conjunct2]])
    have fixed:
      "mean_logistic_step eta q (ln (q / p)) = ln (q / p)"
      by (rule mean_logistic_step_fixed_point[OF p_positive q_positive total])
    have next_upper: "mean_logistic_step eta q ?w \<le> ln (q / p)"
      using upper_monotone fixed by linarith
    show ?case unfolding step_recurrence using next_nonnegative next_upper by blast
  qed
  show "0 \<le> mean_logistic_state eta q k" using interval by blast
  show "mean_logistic_state eta q k \<le> ln (q / p)" using interval by blast
qed

lemma mean_logistic_state_lower_bound:
  fixes eta p q :: real
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and total: "p + q = 1"
    and p_less_q: "p < q"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
  shows "ln (q / p) * (1 - (1 - eta * p * q)^N) \<le>
    mean_logistic_state eta q N"
proof -
  let ?wstar = "ln (q / p)"
  let ?c = "1 - eta * p * q"
  have pq_nonnegative: "0 \<le> p * q"
    by (rule mult_nonneg_nonneg) (use p_positive q_positive in linarith)+
  have eta_pq_le_four_pq: "eta * (p * q) \<le> 4 * (p * q)"
    by (rule mult_right_mono[OF eta_at_most_four pq_nonnegative])
  have four_pq: "4 * (p * q) \<le> 1"
    using four_pq_le_one[OF total] by (simp add: mult.assoc)
  have eta_pq_le_one: "eta * p * q \<le> 1"
    using eta_pq_le_four_pq four_pq by (simp add: mult.assoc)
  have c_nonnegative: "0 \<le> ?c" using eta_pq_le_one by linarith
  have fixed_sigmoid: "sigmoid ?wstar = q"
    by (rule sigmoid_log_odds[OF p_positive q_positive total])
  have error_bound:
    "?wstar - mean_logistic_state eta q k \<le> ?c^k * ?wstar"
    for k
  proof (induction k)
    case 0
    show ?case by (simp add: mean_logistic_state_def)
  next
    case (Suc k)
    let ?w = "mean_logistic_state eta q k"
    have w_nonnegative: "0 \<le> ?w"
      by (rule mean_logistic_state_interval(1)[OF p_positive q_positive total
        p_less_q eta_nonnegative eta_at_most_four])
    have w_upper: "?w \<le> ?wstar"
      by (rule mean_logistic_state_interval(2)[OF p_positive q_positive total
        p_less_q eta_nonnegative eta_at_most_four])
    have slope:
      "p * q * (?wstar - ?w) \<le> sigmoid ?wstar - sigmoid ?w"
      by (rule sigmoid_strong_slope_on_log_odds[OF p_positive q_positive total
        p_less_q w_nonnegative w_upper order_refl])
    have slope_q:
      "p * q * (?wstar - ?w) \<le> q - sigmoid ?w"
      using slope fixed_sigmoid by simp
    have scaled_slope:
      "eta * (p * q * (?wstar - ?w)) \<le>
        eta * (q - sigmoid ?w)"
      by (rule mult_left_mono[OF slope_q eta_nonnegative])
    have recurrence:
      "?wstar - mean_logistic_state eta q (Suc k) =
        (?wstar - ?w) - eta * (q - sigmoid ?w)"
      by (simp add: mean_logistic_state_def funpow_Suc_right
        mean_logistic_step_def)
    have one_step:
      "?wstar - mean_logistic_state eta q (Suc k) \<le>
        ?c * (?wstar - ?w)"
      unfolding recurrence using scaled_slope by (simp add: algebra_simps)
    have scaled_induction:
      "?c * (?wstar - ?w) \<le> ?c * (?c^k * ?wstar)"
      by (rule mult_left_mono[OF Suc.IH c_nonnegative])
    have "?wstar - mean_logistic_state eta q (Suc k) \<le>
        ?c * (?c^k * ?wstar)"
      by (rule order_trans[OF one_step scaled_induction])
    then show ?case by (simp add: mult.assoc)

  qed
  have final_error:
    "?wstar - mean_logistic_state eta q N \<le> ?c^N * ?wstar"
    by (rule error_bound)
  show ?thesis using final_error by (simp add: algebra_simps)
qed

lemma uniform_probability_mono:
  assumes finite_Omega: "finite Omega"
    and subset: "A \<subseteq> B"
  shows "uniform_probability Omega A \<le> uniform_probability Omega B"
proof (cases "Omega = {}")
  case True
  then show ?thesis by (simp add: uniform_probability_def)
next
  case False
  have card_Omega_positive: "0 < card Omega"
    using finite_Omega False by (metis card_gt_0_iff)
  have denominator_positive: "0 < real (card Omega)"
    using card_Omega_positive by simp
  have cardinality:
    "card (Omega \<inter> A) \<le> card (Omega \<inter> B)"
    by (rule card_mono) (use finite_Omega subset in auto)
  have real_cardinality:
    "real (card (Omega \<inter> A)) \<le> real (card (Omega \<inter> B))"
    using cardinality by simp
  show ?thesis
    unfolding uniform_probability_def
    by (rule divide_right_mono[OF real_cardinality])
      (use denominator_positive in linarith)
qed

lemma uniform_probability_complement:
  assumes finite_Omega: "finite Omega"
    and nonempty_Omega: "Omega \<noteq> {}"
  shows "uniform_probability Omega (- E) =
    1 - uniform_probability Omega E"
proof -
  have complement_identity:
    "Omega \<inter> (- E) = Omega - (Omega \<inter> E)" by blast
  have intersection_subset: "Omega \<inter> E \<subseteq> Omega" by blast
  have finite_intersection: "finite (Omega \<inter> E)"
    by (meson finite_Omega finite_subset intersection_subset)
  have card_complement:
    "card (Omega \<inter> (- E)) = card Omega - card (Omega \<inter> E)"
    unfolding complement_identity
    by (rule card_Diff_subset[OF finite_intersection intersection_subset])
  have cardinality_le: "card (Omega \<inter> E) \<le> card Omega"
    by (rule card_mono[OF finite_Omega intersection_subset])
  have card_Omega_positive: "0 < card Omega"
    using finite_Omega nonempty_Omega by (metis card_gt_0_iff)
  have denominator_nonzero: "real (card Omega) \<noteq> 0"
    using card_Omega_positive by simp
  have cast_difference:
    "real (card Omega - card (Omega \<inter> E)) =
      real (card Omega) - real (card (Omega \<inter> E))"
    using cardinality_le by simp
  show ?thesis
    unfolding uniform_probability_def card_complement
    using cast_difference denominator_nonzero
    by (simp add: divide_simps)
qed

lemma finite_binary_orders [simp]: "finite (binary_orders n N)"
  unfolding binary_orders_def by simp

lemma binary_orders_nonempty:
  assumes sample_size: "n \<le> N"
  shows "binary_orders n N \<noteq> {}"
proof -
  let ?xs = "replicate n True @ replicate (N - n) False"
  have "?xs \<in> binary_orders n N"
    unfolding binary_orders_def permutations_of_multiset_def by simp
  then show ?thesis by blast
qed

definition random_order_lower_margin ::
    "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "random_order_lower_margin eta n m N delta =
    ln ((real n / real N) / (real m / real N)) *
      (1 - (1 - eta * (real m / real N) * (real n / real N))^N) -
    eta * sqrt (real N / 2 * ln (2 * real N / delta))"

lemma binary_logistic_state_random_order_lower_bound:
  fixes eta delta :: real
  assumes N_positive: "0 < N"
    and counts: "m + n = N"
    and minority_positive: "0 < m"
    and minority_smaller: "m < n"
    and xs_order: "xs \<in> binary_orders n N"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and prefix_good:
      "binary_max_centered_prefix n N xs <
        sqrt (real N / 2 * ln (2 * real N / delta))"
  shows "random_order_lower_margin eta n m N delta \<le>
    binary_logistic_state eta (real n / real N) xs N"
proof -
  let ?p = "real m / real N"
  let ?q = "real n / real N"
  let ?u = "sqrt (real N / 2 * ln (2 * real N / delta))"
  let ?mean = "mean_logistic_state eta ?q N"
  let ?actual = "binary_logistic_state eta ?q xs N"
  have sample_size: "n \<le> N" using counts by linarith
  have real_N_positive: "0 < real N" using N_positive by simp
  have n_positive: "0 < n" using minority_positive minority_smaller by linarith
  have p_positive: "0 < ?p"
    by (rule divide_pos_pos) (use minority_positive real_N_positive in simp_all)
  have q_positive: "0 < ?q"
    by (rule divide_pos_pos) (use n_positive real_N_positive in simp_all)
  have cast_counts: "real m + real n = real N"
    using arg_cong[OF counts, of "\<lambda>k. real k"] by simp

  have total: "?p + ?q = 1"
    using cast_counts real_N_positive
    by (simp add: add_divide_distrib[symmetric])
  have cast_minority: "real m < real n"
    using minority_smaller by simp
  have p_less_q: "?p < ?q"
    by (rule divide_strict_right_mono[OF cast_minority real_N_positive])
  have mean_lower:
    "ln (?q / ?p) * (1 - (1 - eta * ?p * ?q)^N) \<le> ?mean"
    by (rule mean_logistic_state_lower_bound[OF p_positive q_positive total
      p_less_q eta_nonnegative eta_at_most_four])
  have comparison:
    "abs (?actual - ?mean) \<le>
      eta * binary_max_centered_prefix n N xs"
    by (rule binary_logistic_mean_comparison[OF N_positive sample_size xs_order
      eta_nonnegative eta_at_most_four])
  have mean_actual_gap:
    "?mean - ?actual \<le> eta * binary_max_centered_prefix n N xs"
    using comparison abs_ge_minus_self[of "?actual - ?mean"] by linarith
  have scaled_prefix:
    "eta * binary_max_centered_prefix n N xs \<le> eta * ?u"
    by (rule mult_left_mono) (use prefix_good eta_nonnegative in linarith)+
  have actual_from_mean: "?mean - eta * ?u \<le> ?actual"
    using mean_actual_gap scaled_prefix by linarith
  have "ln (?q / ?p) * (1 - (1 - eta * ?p * ?q)^N) - eta * ?u
      \<le> ?actual"
    using mean_lower actual_from_mean by linarith
  then show ?thesis
    unfolding random_order_lower_margin_def by simp
qed

lemma uniform_binary_order_logistic_confidence:
  fixes eta delta :: real
  assumes N_positive: "0 < N"
    and counts: "m + n = N"
    and minority_positive: "0 < m"
    and minority_smaller: "m < n"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and delta_positive: "0 < delta"
    and delta_at_most_one: "delta \<le> 1"
  shows "1 - delta \<le> uniform_probability (binary_orders n N)
    {xs. random_order_lower_margin eta n m N delta \<le>
      binary_logistic_state eta (real n / real N) xs N}"
proof -
  let ?Omega = "binary_orders n N"
  let ?u = "sqrt (real N / 2 * ln (2 * real N / delta))"
  let ?bad = "{xs. ?u \<le> binary_max_centered_prefix n N xs}"
  let ?good = "{xs. random_order_lower_margin eta n m N delta \<le>
    binary_logistic_state eta (real n / real N) xs N}"
  have sample_size: "n \<le> N" using counts by linarith
  have bad_bound: "uniform_probability ?Omega ?bad \<le> delta"
    by (rule uniform_binary_order_max_prefix_confidence[OF N_positive sample_size
      delta_positive delta_at_most_one])
  have Omega_nonempty: "?Omega \<noteq> {}"
    by (rule binary_orders_nonempty[OF sample_size])
  have complement_probability:
    "uniform_probability ?Omega (- ?bad) =
      1 - uniform_probability ?Omega ?bad"
    by (rule uniform_probability_complement[OF finite_binary_orders Omega_nonempty])
  have complement_lower:
    "1 - delta \<le> uniform_probability ?Omega (- ?bad)"
    using bad_bound complement_probability by linarith
  have event_subset: "?Omega \<inter> (- ?bad) \<subseteq> ?good"
  proof
    fix xs
    assume member: "xs \<in> ?Omega \<inter> (- ?bad)"
    have xs_order: "xs \<in> binary_orders n N" using member by simp
    have prefix_good:
      "binary_max_centered_prefix n N xs < ?u"
      using member by simp
    show "xs \<in> ?good"
      by simp (rule binary_logistic_state_random_order_lower_bound[OF
        N_positive counts minority_positive minority_smaller xs_order
        eta_nonnegative eta_at_most_four prefix_good])
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

lemma uniform_binary_order_positive_margin:
  fixes eta delta :: real
  assumes N_positive: "0 < N"
    and counts: "m + n = N"
    and minority_positive: "0 < m"
    and minority_smaller: "m < n"
    and eta_nonnegative: "0 \<le> eta"
    and eta_at_most_four: "eta \<le> 4"
    and delta_positive: "0 < delta"
    and delta_at_most_one: "delta \<le> 1"
    and margin_positive:
      "0 < random_order_lower_margin eta n m N delta"
  shows "1 - delta \<le> uniform_probability (binary_orders n N)
    {xs. 0 < binary_logistic_state eta (real n / real N) xs N}"
proof -
  let ?Omega = "binary_orders n N"
  let ?bounded = "{xs. random_order_lower_margin eta n m N delta \<le>
    binary_logistic_state eta (real n / real N) xs N}"
  let ?positive = "{xs. 0 < binary_logistic_state eta (real n / real N) xs N}"
  have confidence: "1 - delta \<le> uniform_probability ?Omega ?bounded"
    by (rule uniform_binary_order_logistic_confidence[OF N_positive counts
      minority_positive minority_smaller eta_nonnegative eta_at_most_four
      delta_positive delta_at_most_one])
  have subset: "?bounded \<subseteq> ?positive"
    using margin_positive by auto
  have monotone:
    "uniform_probability ?Omega ?bounded \<le>
      uniform_probability ?Omega ?positive"
    by (rule uniform_probability_mono[OF finite_binary_orders subset])
  show ?thesis using confidence monotone by linarith
qed


end
