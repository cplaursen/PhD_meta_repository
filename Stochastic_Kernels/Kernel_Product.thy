theory Kernel_Product
  imports Kernel Extras "Standard_Borel_Spaces.Lemmas_StandardBorel"
begin

(* TODO: works, but could be better as something like (\<lambda>x. PiE {i} (\<lambda>_. x)) ` sets M *)

text \<open> Klenke theorem 14.25 \<close>

definition pair_kernel :: "('a, 'b) kernel \<Rightarrow> ('a \<times> 'b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>K)" 90) where
"pair_kernel K_1 K_2 \<equiv> kernel_of (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
  (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))\<partial>kernel_measure K_1 \<omega>\<^sub>0)"

lemma pair_kernel_source[simp]: "kernel_source (K_1 \<Otimes>\<^sub>K K_2) = kernel_source K_1"
  unfolding pair_kernel_def by simp

lemma pair_kernel_target[simp]: "kernel_target (K_1 \<Otimes>\<^sub>K K_2) = (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
  unfolding pair_kernel_def by simp

definition pair_kernel_partial :: "('a, 'b) kernel \<Rightarrow> ('b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>P)" 90) where
"pair_kernel_partial K_1 K_2 \<equiv> K_1 \<Otimes>\<^sub>K (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2)
 (\<lambda>\<omega> A\<^sub>2. kernel K_2 (snd \<omega>) A\<^sub>2))"

lemma pair_kernel_partial_source[simp]: "kernel_source (K_1 \<Otimes>\<^sub>P K_2) = kernel_source K_1"
  unfolding pair_kernel_partial_def by simp

lemma pair_kernel_partial_target[simp]: "kernel_target (K_1 \<Otimes>\<^sub>P K_2) = (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
  unfolding pair_kernel_partial_def by simp

lemma
  assumes "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  shows measurable_pair_fst[measurable]: "\<And>x. x \<in> space M1 \<Longrightarrow> {a. (x,a) \<in> A} \<in> sets M2"
    and measurable_pair_snd[measurable]: "\<And>x. x \<in> space M2 \<Longrightarrow> {a. (a,x) \<in> A} \<in> sets M1"
proof -
  have "A \<in> sigma_sets (space M1 \<times> space M2) {(a \<times> b)| a b . a\<in> sets M1 \<and> b \<in> sets M2}"
    using assms sets_pair_measure by blast
  then show "\<And>x. x \<in> space M1 \<Longrightarrow> {a. (x,a) \<in> A} \<in> sets M2"
            "\<And>x. x \<in> space M2 \<Longrightarrow> {a. (a,x) \<in> A} \<in> sets M1"
  proof induct
    case (Basic a)
    then show "\<And>x. {y. (x, y) \<in> a} \<in> sets M2" "\<And>x. {y. (y, x) \<in> a} \<in> sets M1"
      by (auto, smt (verit) mem_Collect_eq set_eq_iff sets.sets_Collect(5))
  next
    case Empty
    then show "\<And>x. {a. (x, a) \<in> {}} \<in> sets M2" "\<And>x. {a. (a, x) \<in> {}} \<in> sets M1" by auto
  next
    case (Compl a)
    then have "\<And>x. x \<in> space M1 \<Longrightarrow> space M2 - {y. (x, y) \<in> a} \<in> sets M2"
      by auto
    moreover have "\<And>x. x \<in> space M2 \<Longrightarrow> space M1 - {y. (y, x) \<in> a} \<in> sets M1"
      using Compl by auto
    ultimately show 
        "\<And>x. x \<in> space M1 \<Longrightarrow> {y. (x, y) \<in> space M1 \<times> space M2 - a} \<in> sets M2"
        "\<And>x. x \<in> space M2 \<Longrightarrow> {y. (y, x) \<in> space M1 \<times> space M2 - a} \<in> sets M1"
      apply auto
      by (smt (verit, ccfv_SIG) Collect_cong assms(1) mem_Collect_eq set_diff_eq)+
  next
    case (Union a)
    then have "\<And>x. x \<in> space M1 \<Longrightarrow> (\<Union>i. {y. (x, y) \<in> a i}) \<in> sets M2"
      by auto
    moreover have "\<And>x. x \<in> space M2 \<Longrightarrow> (\<Union>i. {y. (y, x) \<in> a i}) \<in> sets M1"
      using Union by auto
    ultimately show "\<And>x. x \<in> space M1 \<Longrightarrow> {y. (x, y) \<in> \<Union> (range a)} \<in> sets M2"
                    "\<And>x. x \<in> space M2 \<Longrightarrow> {y. (y, x) \<in> \<Union> (range a)} \<in> sets M1"
      by (auto simp: Collect_ex_eq)
  qed
qed

text \<open> Required for monotone convergence in the below theorem \<close>

lemma kernel_snd_measurable:
  fixes K :: "('a\<times>'b, 'c) kernel"
  assumes A_sets: "A \<in> sets (M1 \<Otimes>\<^sub>M kernel_target K)"
  and sets_eq: "sets (kernel_source K) = sets (M0 \<Otimes>\<^sub>M M1)"
  and \<omega>\<^sub>0: "\<omega>\<^sub>0 \<in> space M0"
  and finite_kernel: "finite_kernel K"
  shows "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
proof -
  define M2 where "M2 \<equiv> kernel_target K"
  let ?G = "{x \<times> y | x y. x \<in> sets M1 \<and> y \<in> sets M2}"
  have sigma_G: "sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G = sets (M1 \<Otimes>\<^sub>M M2)"
    by (metis sets_pair_measure space_pair_measure)
  have "Int_stable ?G"
    using Int_stable_pair_measure_generator by blast
  moreover have "?G \<subseteq> Pow (space (M1 \<Otimes>\<^sub>M M2))"
    by (simp add: pair_measure_closed space_pair_measure)
  moreover have "A \<in> sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G"
    using M2_def A_sets sigma_G by blast
  ultimately show ?thesis
  proof (induct rule: sigma_sets_induct_disjoint)
    case (basic A)
    then obtain x y where xy: "A = x \<times> y" "x \<in> sets M1"  "y \<in> sets M2"
    by blast
    then have "w \<in> x \<Longrightarrow> {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A} = y" for w
      by blast
    moreover have "w \<notin> x \<Longrightarrow> {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A} = {}" for w
      using xy by blast
    moreover have "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) A') \<in> borel_measurable M1" if "A' \<in> sets M2" for A'
      using assms that M2_def by (measurable, auto)
    ultimately show "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
      using xy apply auto
      apply measurable
        apply (smt (verit, ccfv_SIG) M2_def empty_Collect_eq mem_Collect_eq sets.empty_sets subsetI subset_antisym)
      using assms(2,3) apply force
      unfolding pred_def by auto
  next
    case empty
    then show ?case by simp
  next
    case (compl A)
    {
      fix w assume w: "w \<in> space M1"
      then have space: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> space (M1 \<Otimes>\<^sub>M M2)} = space M2"
        unfolding space_pair_measure by auto
      from w have "(\<omega>\<^sub>0, w) \<in> space (kernel_source K)"
        by (metis assms(2,3) SigmaI sets_eq_imp_space_eq space_pair_measure)
      then have "finite_measure (kernel_measure K (\<omega>\<^sub>0, w))"
        by (simp add: finite_kernel.finite_measures finite_kernel)
      then have "kernel_measure K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = 
          kernel_measure K (\<omega>\<^sub>0, w) (space M2) - kernel_measure K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        unfolding M2_def apply (subst kernel_measure_space[THEN sym])+
        apply (rule emeasure_compl)
        using sigma_G compl M2_def w apply force
        by (metis finite_measure.emeasure_finite infinity_ennreal_def)
      then have "K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = K (\<omega>\<^sub>0, w) (space M2) - K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        using kernel_measure_emeasure by metis
    } note diff = this
    have space_eq: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> space (M1 \<Otimes>\<^sub>M M2)} = space M2" if "w \<in> space M1" for w
      by (simp add: that space_pair_measure)
    have "(\<lambda>w. K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A})) \<in> borel_measurable M1"
      apply (subst measurable_cong[OF diff])
       apply simp
      unfolding M2_def using sets_eq apply measurable
      using \<omega>\<^sub>0 apply simp
       apply auto
      using compl by simp
    then show ?case
      apply (subst measurable_cong[where g="(\<lambda>w. K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}))"])
       apply (smt (verit, best) Collect_cong Diff_iff mem_Collect_eq minus_set_def space_eq)
      apply simp 
      done
  next
    case (union A)
    {
      fix w assume w: "w \<in> space M1"
      then have "(\<omega>\<^sub>0, w) \<in> space (kernel_source K)"
        using \<omega>\<^sub>0 sets_eq_imp_space_eq[OF sets_eq] space_pair_measure by blast
      then have "measure_space (space M2) (sets M2) (kernel K (\<omega>\<^sub>0, w))"
        using kernel.space_source_measure unfolding M2_def by fast
      then have countably_additive: "countably_additive (sets M2) (kernel K (\<omega>\<^sub>0, w))"
        unfolding measure_space_def by blast
      have 1: "range (\<lambda>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i}) \<subseteq> sets M2"
        using union(2) sigma_G w unfolding M2_def by force
      have 2: "disjoint_family (\<lambda>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        using union(1) unfolding disjoint_family_on_def by auto
      have 3: "(\<Union>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i}) \<in> sets M2"
        using 1 by blast
      have 4: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)} = (\<Union>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        by blast
      have "kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)} = (\<Sum>i. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        using countably_additive 1 2 3 4 unfolding countably_additive_def by presburger
    } note additive = this
    then show "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)}) \<in> borel_measurable M1"
      apply (subst measurable_cong[OF additive])
       apply simp
      using borel_measurable_suminf union by auto
  qed
qed

text \<open> Klenke theorem 14.25 \<close>

theorem pair_kernel_transition_kernel:
  fixes K_1 :: "('a, 'b) kernel"
    and K_2 :: "('a\<times>'b, 'c) kernel"
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "transition_kernel (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
    (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
  (is "transition_kernel ?\<Omega>\<^sub>1 ?\<Omega>\<^sub>2 ?\<kappa>")
proof (intro transition_kernel.intro)
  let ?M0 = "kernel_source K_1"
  and ?M1 = "kernel_target K_1"
  and ?M2 = "kernel_target K_2"

  let ?f = "(\<lambda>A'. \<lambda>(\<omega>\<^sub>1, \<omega>\<^sub>2). indicator A' (snd \<omega>\<^sub>1, \<omega>\<^sub>2))"
  let ?g = "\<lambda>f. (\<lambda> x. \<integral>\<^sup>+\<omega>\<^sub>2. f (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 x)"

  fix A' assume A': "A' \<in> sets (?M1 \<Otimes>\<^sub>M ?M2)"
  have "?f A' \<in> borel_measurable ((?M0 \<Otimes>\<^sub>M ?M1) \<Otimes>\<^sub>M ?M2)"
    apply measurable
    unfolding pred_def using A' by simp
  then have "(\<lambda> x. \<integral>\<^sup>+\<omega>\<^sub>2. ?f A' (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 x) \<in> borel_measurable (?M0 \<Otimes>\<^sub>M ?M1)"
    apply measurable
      apply (metis eq measurable_ident_sets sets_pair_measure_cong)
      apply (simp add: finite(2))
      using eq measurable_ident_sets apply blast
    done
  then show "(\<lambda>\<omega>\<^sub>0. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A' (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) \<in> borel_measurable (kernel_source K_1)"
    apply simp
    by (smt (verit, best) kernel_measure_pair_integral_measurable local.finite(1) measurable_cong nn_integral_cong snd_conv)
next
  fix \<omega>\<^sub>0 assume *: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
  have "countably_additive (sets ?\<Omega>\<^sub>2) (?\<kappa> \<omega>\<^sub>0)"
  proof (auto simp add: countably_additive_def)
    fix A :: "nat \<Rightarrow> ('b \<times> 'c) set"
    assume range: "range A \<subseteq> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
          and disj: "disjoint_family A"
    have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (\<Union> (range A)) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
        \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Sum>n. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      by (simp add: suminf_indicator[OF disj, THEN sym])
    also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. (\<Sum>n. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      apply (rule nn_integral_cong)
      apply (rule nn_integral_suminf)
      apply measurable
      unfolding pred_def using range apply simp
      done
    also have "... = (\<Sum>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A i) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
    proof (rule nn_integral_suminf)
      fix n
      have A_n_measurable [measurable]: "A n \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
        using range by auto
      then have A_n_sigma: "A n \<in> sigma_sets (space (kernel_target K_1) \<times> space (kernel_target K_2))
 {a \<times> b |a b. a \<in> sets (kernel_target K_1) \<and> b \<in> sets (kernel_target K_2)}"
        using sets_pair_measure by blast
      {
        fix \<omega>\<^sub>1 assume \<omega>\<^sub>1: "\<omega>\<^sub>1 \<in> space (kernel_measure K_1 \<omega>\<^sub>0)"
        define A' where "A' = {\<omega>\<^sub>2. (\<omega>\<^sub>1, \<omega>\<^sub>2) \<in> A n}"
        have "(\<lambda>\<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2)) = indicator A'"
          unfolding A'_def indicator_def by auto
        then have "(\<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))
                 = (\<integral>\<^sup>+ \<omega>\<^sub>2. indicator A' \<omega>\<^sub>2 \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))"
          by (simp add: A'_def indicator_def)
        also have "... = emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) A'"
          apply (rule nn_integral_indicator)
          unfolding A'_def using A_n_measurable \<omega>\<^sub>1 by auto
        finally have "(\<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) =
                             emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) A'"
          .
      } note A = this
      moreover have "(\<lambda>w. kernel K_2 (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A n}) \<in> borel_measurable (kernel_measure K_1 \<omega>\<^sub>0)"
        by (simp add: measurable_kernel_measure kernel_snd_measurable[OF A_n_measurable eq * finite(2)])
      ultimately show "(\<lambda>x. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, x)) \<in> borel_measurable (kernel_measure K_1 \<omega>\<^sub>0)"
        by (smt (verit, ccfv_SIG) kernel_measure_emeasure measurable_cong)
    qed
    finally show "(\<Sum>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A i) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (\<Union> (range A)) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      ..
  qed
  then show "measure_space (space ?\<Omega>\<^sub>2) (sets ?\<Omega>\<^sub>2) (?\<kappa> \<omega>\<^sub>0)"
    unfolding measure_space_def apply auto                                                          
    using sets.sigma_algebra_axioms apply blast
    unfolding positive_def by auto
qed

corollary kernel_prod_apply:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
      and "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" "A \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
    shows "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 A = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
  unfolding pair_kernel_def
  apply (rule kernel_apply_kernel_of[OF assms(4,5)])
  by (rule pair_kernel_transition_kernel[OF assms(1-3)])

lemma kernel_prod_partial_transition_kernel:
  fixes K_1 :: "('a, 'b) kernel"
    and K_2 :: "('b, 'c) kernel"
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_target K_1)"
    shows "transition_kernel (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
    (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
proof -
  have 1: "kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2)
   (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) = kernel_measure K_2 \<omega>\<^sub>1"
    if "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" for \<omega>\<^sub>0 \<omega>\<^sub>1
    apply (simp add: kernel_measure_altdef)
  apply (rule measure_of_eq)
   apply (rule sets.space_closed)
  apply (simp add: sets.sigma_sets_eq)
  apply (cases "\<omega>\<^sub>1 \<in> space (kernel_source K_2)")
   apply (subst kernel_apply_kernel_of)
      apply (auto simp: space_pair_measure)
  unfolding transition_kernel_def
  apply (simp_all add: that)
  apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
  done
  have 2: "(\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
  \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
    for \<omega>\<^sub>0 A
    apply (cases "\<omega>\<^sub>0 \<in> space (kernel_source K_1)")
    apply (rule nn_integral_cong)
     apply (simp add: 1)
    apply (simp add: kernel_measure_notin_space)
    by (metis nn_integral_null_measure null_measure_def)
  show ?thesis
    apply (subst 2)
    using pair_kernel_transition_kernel[of K_1 "kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))"]
    apply simp
    using finite eq
    by (smt (verit) 1 SigmaE finite_kernel.finite_measures finite_kernelI sets_pair_measure_cong source_kernel_of space_pair_measure)
qed

corollary kernel_prod_partial_apply:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_target K_1)"
      and in_space: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
      and in_sets: "A \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
    shows "kernel (K_1 \<Otimes>\<^sub>P K_2) \<omega>\<^sub>0 A = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
proof -
  have 1: "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2)
                 (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
    \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      if "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" for \<omega>\<^sub>0 A
    apply (rule nn_integral_cong)
    subgoal for x
      apply (intro arg_cong[where f="\<lambda>M. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (x, \<omega>\<^sub>2) \<partial>M"])
      using that apply (subst kernel_measure_kernel_of)
        apply (simp add: space_pair_measure eq[THEN sets_eq_imp_space_eq])
       apply (intro transition_kernel.intro)
        apply (measurable, assumption)
        apply measurable
       apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
      unfolding kernel_measure_altdef apply simp
      done
    done
  show ?thesis
    unfolding pair_kernel_partial_def pair_kernel_def
  apply (subst kernel_apply_kernel_of[OF in_space])
    using in_sets apply simp
     apply (subst transition_kernel_cong[where g="\<lambda>\<omega>\<^sub>0 A.\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"])
    using 1 apply blast
     apply simp
    using kernel_prod_partial_transition_kernel[OF assms(1-3)] apply blast
    using 1 in_space apply blast
    done
qed

lemma pair_kernel_sigma_finite:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "sigma_finite_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof -
  {
    fix \<omega>\<^sub>0 assume \<omega>: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
    define A where "A \<equiv> (\<lambda>\<omega>\<^sub>0 (n :: nat). {\<omega>\<^sub>1 \<in> space (kernel_target K_1). kernel K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) (space (kernel_target K_2)) < n})"
    then have kernel_leq: "x \<in> (A \<omega>\<^sub>0 n) \<Longrightarrow> kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2)) \<le> n" for x n
      by fastforce
    have A_sets: "A \<omega>\<^sub>0 n \<in> sets (kernel_target K_1)" for n
      unfolding A_def apply measurable
       apply (metis \<omega> eq measurable_Pair1' measurable_cong_sets)
      by simp
    have "countable (range (A \<omega>\<^sub>0))"
      by blast
    have "(kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2))) \<noteq> \<infinity>" for x
      by (simp add: finite_kernel_finite local.finite(2))
    then have *: "x \<in> space (kernel_target K_1) \<Longrightarrow> \<exists>m \<in> {Suc 0..}. (kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2))) < of_nat m" for x
      by (metis Suc_leI atLeast_iff gr0I infinity_ennreal_def not_less_zero of_nat_0 top.not_eq_extremum ennreal_Ex_less_of_nat)
    have "(\<Union>n :: nat \<in> {1..}. A \<omega>\<^sub>0 n) = space (kernel_target K_1)"
      unfolding A_def by (auto simp add: set_eq_iff * )
    have sigma_finite: "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) < \<infinity>" for n :: nat
    proof -
      have "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) = 
 (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))\<partial>kernel_measure K_1 \<omega>\<^sub>0)"
        apply (rule kernel_prod_apply[OF assms \<omega>])
        using A_sets sets_pair_measure by auto
      also have L: "... = \<integral>\<^sup>+ \<omega>\<^sub>1. indicator (A \<omega>\<^sub>0 n) \<omega>\<^sub>1 * emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) (space (kernel_target K_2))
       \<partial>kernel_measure K_1 \<omega>\<^sub>0"
        apply (auto simp: indicator_times A_def)
        apply (subst(2) nn_integral_eq_simple_integral)
        by auto
      also have "... \<le> \<integral>\<^sup>+ \<omega>\<^sub>1. (of_nat n) * indicator (A \<omega>\<^sub>0 n) \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"
        apply (rule nn_integral_mono)
        unfolding A_def
        by (metis (no_types, lifting) indicator_simps(1) indicator_simps(2) kernel_measure_emeasure
            linorder_not_less mem_Collect_eq mult.commute mult.right_neutral mult_zero_right order_less_imp_le)
      also have "... \<le> n * kernel K_1 \<omega>\<^sub>0 (A \<omega>\<^sub>0 n)"
        apply (subst nn_integral_cmult_indicator)
        using A_sets kernel_measure_sets apply fast
        apply (subst kernel_measure_emeasure) ..
      also have "... < \<infinity>"
      by (metis finite_kernel_finite finite(1) ennreal_less_top ennreal_mult_eq_top_iff 
              ennreal_of_nat_eq_real_of_nat infinity_ennreal_def top.not_eq_extremum)
    finally show "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) < \<infinity>"
      by simp
  qed
    let ?A = "range (\<lambda>n. (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)))"
    have "countable ?A \<and>
             ?A \<subseteq> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<and>
             \<Union> ?A = space (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<and>
             (\<forall>a\<in>?A. emeasure (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0) a \<noteq> \<top>)"
      apply auto
      prefer 5 
          apply (metis infinity_ennreal_def top.not_eq_extremum sigma_finite)
      unfolding A_def using assms \<omega> apply measurable
        apply (simp add: space_pair_measure)
      using "*" space_pair_measure apply fastforce
      by (simp add: space_pair_measure)
  }
  then show "sigma_finite_kernel (K_1 \<Otimes>\<^sub>K K_2)"
    apply (intro sigma_finite_kernel.intro sigma_finite_measure.intro)
    by (metis (mono_tags, lifting) infinity_ennreal_def kernel_measure_sets kernel_measure_space pair_kernel_source pair_kernel_target)
qed

lemma pair_kernel_stochastic:    
  assumes stochastic: "stochastic_kernel K_1" "stochastic_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "stochastic_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof (rule stochastic_kernelI)
  fix \<omega> assume *: "\<omega> \<in> space (kernel_source (K_1 \<Otimes>\<^sub>K K_2))"
  have "finite_kernel K_1" "finite_kernel K_2"
    using assms stochastic_kernel.axioms(1) by blast+
  then have "(K_1 \<Otimes>\<^sub>K K_2) \<omega> (space (kernel_target (K_1 \<Otimes>\<^sub>K K_2))) = \<integral>\<^sup>+ \<omega>\<^sub>1. emeasure (kernel_measure K_2 (\<omega>, \<omega>\<^sub>1)) (space (kernel_target K_2)) \<partial>kernel_measure K_1 \<omega>"
    apply (subst kernel_prod_apply)
    using * apply (simp_all add: assms)
    apply (simp add: space_pair_measure indicator_times)
    apply (subst(2) nn_integral_eq_simple_integral)
     apply auto
    apply (rule nn_integral_cong)
    by simp
  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K_1 \<omega>"
    apply (rule nn_integral_cong)
    by (metis (full_types) "*" SigmaI eq kernel_measure_space pair_kernel_source prob_space.emeasure_space_1 sets_eq_imp_space_eq space_pair_measure stochastic(2) stochastic_kernel.probability_measures)
  also have "... = 1"
    using stochastic(1) * prob_space.emeasure_space_1 stochastic_kernel.probability_measures by fastforce
  finally show "prob_space (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>)"
    by (auto intro: prob_spaceI)
qed

(* CARBON COPY OF THE ABOVE *)
lemma pair_kernel_substochastic:    
  assumes substochastic: "substochastic_kernel K_1" "substochastic_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
      and nonempty: "space (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<noteq> {}"
        (* Could remove nonempty assumption with changes to substochastic locale *)
    shows "substochastic_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof (rule substochastic_kernelI)
  fix \<omega> assume *: "\<omega> \<in> space (kernel_source (K_1 \<Otimes>\<^sub>K K_2))"
  have "finite_kernel K_1" "finite_kernel K_2"
    using assms substochastic_kernel.axioms(1) by blast+
  then have "(K_1 \<Otimes>\<^sub>K K_2) \<omega> (space (kernel_target (K_1 \<Otimes>\<^sub>K K_2))) \<le>
   \<integral>\<^sup>+ \<omega>\<^sub>1. emeasure (kernel_measure K_2 (\<omega>, \<omega>\<^sub>1)) (space (kernel_target K_2)) \<partial>kernel_measure K_1 \<omega>"
    apply (subst kernel_prod_apply)
    using * apply (simp_all add: assms)
    apply (simp add: space_pair_measure indicator_times)
    apply (subst(2) nn_integral_eq_simple_integral)
     apply auto
    apply (rule nn_integral_mono)
    by simp
  also have "... \<le>  \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K_1 \<omega>"
    apply (rule nn_integral_mono)
    by (metis substochastic(2) kernel_measure_emeasure kernel_not_space_zero
        linordered_nonzero_semiring_class.zero_le_one subprob_space.subprob_emeasure_le_1 
        substochastic_kernel.subprob_measures)
  also have "... \<le> 1"
    apply simp
    using substochastic
    by (simp add: substochastic_kernel.kernel_leq_1)
  finally show "subprob_space (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>)"
    by (auto intro: subprob_spaceI simp: nonempty)
qed

lemma pair_kernel_partial_stochastic:
  assumes [simp]: "stochastic_kernel K\<^sub>1" "stochastic_kernel K\<^sub>2"
    and [simp]: "sets (kernel_target K\<^sub>1) = sets (kernel_source K\<^sub>2)"
  shows "stochastic_kernel (K\<^sub>1 \<Otimes>\<^sub>P K\<^sub>2)"
  unfolding pair_kernel_partial_def
  using assms(1) apply (rule pair_kernel_stochastic)
   apply (rule stochastic_kernel_kernel_ofI)
    apply (metis SigmaD2 assms(2) prod.collapse space_pair_measure stochastic_kernel.kernel_space_eq_1)
   apply (intro transition_kernel.intro)
    apply measurable
     apply blast
    apply blast
   apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
  apply auto
  done
section \<open> Kernel semidirect product \<close>

lemma semidirect_product_unique:
  assumes space: "x \<in> space M" "y \<in> space M"
    and finite: "finite_measure M" "finite_kernel K"
    and sets: "sets M = sets (kernel_source K)"
  shows "kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) x = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) y"
  unfolding kernel_measure_altdef
  apply (rule arg_cong3[where g=measure_of])
    apply simp_all
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  subgoal for A'
    apply (cases "A' \<in> sets (M \<Otimes>\<^sub>M kernel_target K)")
     apply (subst kernel_prod_partial_apply)
    using finite defer
    using finite apply blast
    using sets apply simp
    using space apply simp
    using sets apply simp
     apply (subst kernel_prod_partial_apply)
    using finite defer
    using finite apply blast
    using sets apply simp
    using space apply simp
    using sets apply simp
    using assms apply simp
      apply simp
    using emeasure_kernel_finite local.finite(1) apply blast+
    done
  done

definition kernel_semidirect_product :: "'a measure \<Rightarrow> ('a, 'b) kernel \<Rightarrow> ('a \<times> 'b) measure" (infixr "(\<Otimes>\<^sub>S)" 70)
  where "M \<Otimes>\<^sub>S K = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) (SOME \<omega>. \<omega> \<in> space (kernel_source K))"

lemma space_kernel_semidirect_product[simp]: "space (M \<Otimes>\<^sub>S K) = (space M \<times> space (kernel_target K))"
  unfolding kernel_semidirect_product_def by (simp add: space_pair_measure)

lemma sets_kernel_semidirect_product[measurable]: "sets (M \<Otimes>\<^sub>S K) = sets (M \<Otimes>\<^sub>M (kernel_target K))"
  unfolding kernel_semidirect_product_def 
  by (simp add: pair_kernel_partial_def)

lemma kernel_semidirect_product_measurable[measurable]: 
  "f \<in> M \<Otimes>\<^sub>S K \<rightarrow>\<^sub>M M' \<longleftrightarrow> f \<in> M \<Otimes>\<^sub>M (kernel_target K) \<rightarrow>\<^sub>M M'"
  using measurable_cong_sets[OF sets_kernel_semidirect_product] by blast

locale finite_measure_kernel = K?: finite_kernel K + M?: finite_measure M
  for K :: "('a, 'b) kernel" and M :: "'a measure" +
  assumes sets_eq: "sets (kernel_source K) = sets M"
      and nonempty: "space M \<noteq> {}"
begin

lemma space_eq: "space (kernel_source K) = space M"
  by (fact sets_eq_imp_space_eq[OF sets_eq])

lemma emeasure_semidirect_product:
  assumes "A \<in> sets (M \<Otimes>\<^sub>S K)"
  shows "emeasure (M \<Otimes>\<^sub>S K) A = \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M"
  unfolding kernel_semidirect_product_def 
  apply (subst kernel_measure_emeasure)
  apply (subst kernel_prod_partial_apply)
  using emeasure_kernel_finite finite_measure_axioms apply blast
  using finite_kernel_axioms apply blast
     apply (simp add: sets_eq)
    apply (simp add: nonempty some_in_eq space_eq)
  using assms apply (simp add: sets_kernel_semidirect_product)
  apply (simp add: nonempty some_in_eq space_eq)
  done

lemma emeasure_times_semidirect_product: 
  assumes "A \<in> sets M" "B \<in> sets (kernel_target K)"
  shows "emeasure (M \<Otimes>\<^sub>S K) (A \<times> B) = (\<integral>\<^sup>+\<omega>\<^sub>1 \<in> A. K \<omega>\<^sub>1 B \<partial>M)"
  apply (subst emeasure_semidirect_product)
  using assms sets_kernel_semidirect_product apply blast
  apply (simp add: indicator_times assms(2) mult.commute nn_integral_cmult_indicator)
  done

lemma kernel_Fubini:
  assumes f[measurable]: "f \<in> borel_measurable (M \<Otimes>\<^sub>M (kernel_target K))"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M)"
using f proof induct
  case (cong f g) 
  have "integral\<^sup>N (M \<Otimes>\<^sub>S K) f = integral\<^sup>N (M \<Otimes>\<^sub>S K) g"
    by (intro nn_integral_cong, simp add: space_pair_measure cong(3))
  moreover have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
                 (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. g (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_cong)+
    using cong(3) space_pair_measure by fastforce
  ultimately show ?case
    using cong(4) by argo
next
  case (set A)
  then show ?case
    by (simp add: emeasure_semidirect_product sets_kernel_semidirect_product)
next
  case (mult u v)
  have L: "(\<integral>\<^sup>+ \<omega>. v * u \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = v * (\<integral>\<^sup>+ \<omega>. u \<omega> \<partial>(M \<Otimes>\<^sub>S K))"
    using nn_integral_cmult kernel_semidirect_product_measurable mult.hyps(2) by blast
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v * u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. v * (\<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (rule nn_integral_cong)
    apply (intro nn_integral_cmult)
     apply (metis mult.hyps(2) measurable_Pair2 measurable_kernel_measure)
    done
  also have "... = v * (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_cmult)
    using mult.hyps(2) sets_eq finite_kernel_axioms by measurable
  finally show ?case
    using L mult.hyps(4) by argo
next
  case (add u v)
  have L: "(\<integral>\<^sup>+ \<omega>. v \<omega> + u \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = (\<integral>\<^sup>+ \<omega>. v \<omega> \<partial>(M \<Otimes>\<^sub>S K)) + (\<integral>\<^sup>+ \<omega>. u \<omega> \<partial>(M \<Otimes>\<^sub>S K))"
    using nn_integral_add kernel_semidirect_product_measurable add.hyps(1,4) by blast
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2) + u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
   \<integral>\<^sup>+ \<omega>\<^sub>1. (\<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) + (\<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (intro nn_integral_cong nn_integral_add)
    using add.hyps(1,4) apply measurable
  done
  also have "... = (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) 
                 + (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_add)
    using add.hyps(1,4) sets_eq finite_kernel_axioms by measurable
  finally show ?case
    using L add.hyps(3,7) by argo
  next
  case (seq U)
  then have 1: "\<And>i. U i \<in> borel_measurable (M \<Otimes>\<^sub>S K)"
    using kernel_semidirect_product_measurable by blast
  have "integral\<^sup>N (M \<Otimes>\<^sub>S K) (\<Squnion> range U) = \<integral>\<^sup>+ x. (\<Squnion>i. U i x) \<partial>(M \<Otimes>\<^sub>S K)"
    by (intro nn_integral_cong SUP_apply)
  then have L: "integral\<^sup>N (M \<Otimes>\<^sub>S K) (\<Squnion> range U) = (\<Squnion>i. integral\<^sup>N (M \<Otimes>\<^sub>S K) (U i))"
    by (simp add: nn_integral_monotone_convergence_SUP[OF seq(4) 1])
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Squnion> range U) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Squnion>i. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M"
    by (subst SUP_apply, argo)
  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. (\<Squnion>i. \<integral>\<^sup>+ \<omega>\<^sub>2. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (intro nn_integral_cong nn_integral_monotone_convergence_SUP)
    using seq(4) mono_compose apply blast
    apply (metis measurable_Pair2 measurable_kernel_measure seq.hyps(1))
    done
  also have "... = (\<Squnion>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (intro nn_integral_monotone_convergence_SUP)
    using seq(4) apply (simp add: incseq_def le_fun_def nn_integral_mono)
    apply measurable
    using seq.hyps(1) sets_eq finite_kernel_axioms apply auto
    done
  finally show ?case
    using L seq(3) by presburger
qed

end

section \<open> Finite product kernel\<close>

primrec PiK :: "nat \<Rightarrow> (nat \<Rightarrow> ('a, 'a) kernel) \<Rightarrow> ('a, (nat \<Rightarrow> 'a)) kernel" where
"PiK 0 K = kernel_of (kernel_source (K 0)) (PiM {0} (\<lambda>i. kernel_target (K i)))
   (\<lambda> \<omega> A'. (K 0) \<omega> ((\<lambda>x.(\<lambda>n\<in>{0}. x)) -` A' \<inter> space (kernel_target (K 0))))" |
"PiK (Suc n) K = kernel_of (kernel_source (K 0)) (PiM {0..Suc n} (\<lambda>i. kernel_target (K i)))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (Suc n:=\<omega>)) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"

text \<open> We'll want to use @{thm distr_PiM_reindex} to update the target set of the product kernel \<close>
thm distr_PiM_reindex

lemma PiK_source[simp]: "kernel_source (PiK n K) = kernel_source (K 0)"
  by (cases n; simp)

lemma PiK_target[simp]: "kernel_target (PiK n K) = PiM {0..n} (\<lambda>i. kernel_target (K i))"
  by (cases n; simp)

lemma transition_kernel_PiK_0:
  fixes K :: "nat \<Rightarrow> ('a,'a) kernel"
  shows "transition_kernel (kernel_source (K 0)) (PiM {0} (\<lambda>i. kernel_target (K i)))
    (\<lambda> \<omega> A'. (K 0) \<omega> (((\<lambda>x.(\<lambda>n\<in>{0}. x)) -` A') \<inter> space (kernel_target (K 0))))"
proof (intro transition_kernel.intro, goal_cases)
  case (1 A')
  then show ?case
    apply measurable
    using 1 by (subst sets_PiM_cong[where J="{0}" and N="\<lambda>i. kernel_target (K i)"]; simp)
next
  case (2 \<omega>)
  then have *: "countably_additive (sets (kernel_target (K 0))) (K 0 \<omega>)"
    by (rule kernel.countably_additive)
  have "countably_additive (sets (Pi\<^sub>M {0} (\<lambda>n. kernel_target (K n))))
     (\<lambda>A'. kernel (K 0) \<omega> ((\<lambda>x. \<lambda>n\<in>{0}. x) -` A' \<inter> space (kernel_target (K 0))))"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) set"
    assume A: "range A \<subseteq> sets (Pi\<^sub>M {0} (\<lambda>n. kernel_target (K n)))"
         "disjoint_family A"
         "\<Union> (range A) \<in> sets (Pi\<^sub>M {0} (\<lambda>n. kernel_target (K n)))"
    have range: "range (\<lambda>i. (\<lambda>x. \<lambda>n\<in>{0}. x) -` A i \<inter> space (kernel_target (K 0))) \<subseteq> sets (kernel_target (K 0))"
      apply safe
      apply measurable
      by (smt (verit, ccfv_threshold) A(1) range_subsetD sets_PiM_cong singletonD)
    moreover have "disjoint_family (\<lambda>i. (\<lambda>x. \<lambda>n\<in>{0}. x) -` A i \<inter> space (kernel_target (K 0)))"
      using A(2) unfolding disjoint_family_on_def by auto
    moreover have "(\<Union>i. (\<lambda>x. \<lambda>n\<in>{0}. x) -` A i \<inter> space (kernel_target (K 0))) \<in> sets (kernel_target (K 0))"
      using range by blast
    ultimately have "(\<Sum>i. kernel (K 0) \<omega> ((\<lambda>x. \<lambda>n\<in>{0}. x) -` A i \<inter> space (kernel_target (K 0)))) = kernel (K 0) \<omega> (\<Union> (range (\<lambda>n. ((\<lambda>x. \<lambda>n\<in>{0}. x) -` (A n) \<inter> space (kernel_target (K 0))))))"
      using * countably_additive_def by blast
    also have "... = kernel (K 0) \<omega> ((\<lambda>x. \<lambda>n\<in>{0}. x) -` \<Union> (range A) \<inter> space (kernel_target (K 0)))"
      by (simp add: vimage_Union)
    finally show "(\<Sum>i. kernel (K 0) \<omega> ((\<lambda>x. \<lambda>n\<in>{0}. x) -` A i \<inter> space (kernel_target (K 0)))) = kernel (K 0) \<omega> ((\<lambda>x. \<lambda>n\<in>{0}. x) -` \<Union> (range A) \<inter> space (kernel_target (K 0)))"
      .
  qed
  then show ?case
    unfolding measure_space_def positive_def
    by (smt (verit, del_insts) kernel_empty sets.Int_space_eq2 sets.empty_sets 
        sets.sigma_algebra_axioms sets_PiM_cong singletonD vimage_empty)
qed

lemma transition_kernel_PiK_Suc:
  fixes K :: "nat \<Rightarrow> ('a, 'a) kernel"
  assumes finite: "finite_kernel (PiK n K)" "finite_kernel (K (Suc n))"
      and source_eq_target: "kernel_target (K n) = kernel_source (K (Suc n))"
  shows "transition_kernel (kernel_source (K 0)) (kernel_target (PiK (Suc n) K))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>.  indicator A' (\<omega>\<^sub>f (Suc n:=\<omega>)) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)" (is "transition_kernel ?M ?N' ?\<kappa>")
proof -
  have eq: "(kernel_of (kernel_target (PiK n K)) (kernel_target (K (Suc n)))
    (\<lambda>\<omega>. K (Suc n) (\<omega> n))) \<omega>\<^sub>f A' = (K (Suc n)) (\<omega>\<^sub>f n) A'"
    if "\<omega>\<^sub>f \<in> space (kernel_target (PiK n K))" for \<omega>\<^sub>f A'
    apply (cases "A' \<in> sets (kernel_target (K (Suc n)))")
    apply (subst kernel_apply_kernel_of)
       using that apply (auto simp: that)
    apply (intro transition_kernel.intro)
     apply measurable
         apply blast
        apply (metis atLeastAtMost_iff bot_nat_0.extremum dual_order.refl measurable_component_singleton source_eq_target)
       by (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
  have 1: "kernel_measure (kernel_of (kernel_target (PiK n K)) (kernel_target (K (Suc n)))
    (\<lambda>\<omega>. K (Suc n) (\<omega> n))) \<omega>\<^sub>f = kernel_measure (K (Suc n)) (\<omega>\<^sub>f n)"
    if "\<omega>\<^sub>f \<in> space (kernel_target (PiK n K))" for \<omega>\<^sub>f
    apply (simp add: kernel_measure_altdef)
    apply (rule measure_of_eq)
     apply (rule sets.space_closed)
    using that apply (simp add: sets.sigma_sets_eq)
   apply (subst kernel_apply_kernel_of)
       apply (auto simp: space_PiM)
    apply (intro transition_kernel.intro)
     apply measurable
      apply blast
       apply (metis atLeast0AtMost atMost_iff dual_order.eq_iff image_eqI measurable_component_singleton source_eq_target)
    apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
    done
  have 2: "(\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>) = (\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (kernel_of (kernel_target (PiK n K)) (kernel_target (K (Suc n)))
    (\<lambda>\<omega>. K (Suc n) (\<omega> n))) \<omega>\<^sub>f) \<partial>kernel_measure (PiK n K) \<omega>)" for \<omega> A'
    apply (cases "\<omega> \<in> space (kernel_source (K 0))")
     apply (rule nn_integral_cong)
    using 1 apply force
    by (metis (mono_tags, lifting) "1" kernel_measure_space nn_integral_cong)
  have 3: "kernel_target (K (Suc n)) = kernel_target (kernel_of (kernel_target (PiK n K)) (kernel_target (K (Suc n))) (\<lambda>\<omega>. kernel (K (Suc n)) (\<omega> n)))"
    by simp
  have "transition_kernel (kernel_source (PiK n K))
  (kernel_target (PiK n K) \<Otimes>\<^sub>M (kernel_target (K (Suc n))))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"
    apply (subst 2)
    apply (subst 3)
    apply (rule kernel_prod_partial_transition_kernel[of "PiK n K" "kernel_of (kernel_target (PiK n K)) (kernel_target (K (Suc n)))
    (\<lambda>\<omega>. K (Suc n) (\<omega> n))"])
    using finite apply simp_all
    apply (intro finite_kernelI finite_measureI)
    apply auto
    by (smt (verit, best) "1" PiK_target PiM_cong finite_kernel_finite kernel_measure_emeasure)
  then have "transition_kernel (kernel_source (PiK n K)) (kernel_target (PiK (Suc n) K))
    (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator ((\<lambda>(f,y). f(Suc n:=y)) -` A' \<inter> space (kernel_target (PiK n K) \<Otimes>\<^sub>M (kernel_target (K (Suc n))))) (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"
    apply (rule transition_kernel.transition_kernel_distr)
    apply simp
    apply (subst atLeast0_atMost_Suc)
    by measurable
  then have "transition_kernel (kernel_source (PiK n K)) (kernel_target (PiK (Suc n) K))
    (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (Suc n := \<omega>)) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"
    apply (subst transition_kernel_cong[where g="(\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator ((\<lambda>(f,y). f(Suc n:=y)) -` A' \<inter> space (kernel_target (PiK n K) \<Otimes>\<^sub>M (kernel_target (K (Suc n))))) (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"])
     apply (rule nn_integral_cong)
     apply (rule nn_integral_cong)
     apply (smt (verit, best) Int_iff case_prod_conv indicator_simps(1) indicator_simps(2) kernel_measure_space mem_Sigma_iff space_pair_measure vimage_eq)
    by blast
  then show ?thesis by simp
qed

lemma PiK_apply_0:
  assumes "\<omega> \<in> space (kernel_source (K 0))" "A' \<in> sets (PiM {0} (\<lambda>n. kernel_target (K n)))"
  shows "PiK 0 K \<omega> A' = (K 0) \<omega> ((\<lambda>x.(\<lambda>n\<in>{0}. x)) -` A' \<inter> space (kernel_target (K 0)))"
  apply simp
  apply (subst kernel_apply_kernel_of)
  using assms apply simp_all
  using transition_kernel_PiK_0[of K]
  by (smt (verit, best) PiM_cong singletonD transition_kernel_PiK_0 transition_kernel_cong vimage_inter_cong)

lemma PiK_apply_Suc:
  assumes "finite_kernel (PiK n K)" "finite_kernel (K (Suc n))"
    "kernel_target (K n) = kernel_source (K (Suc n))"
    "\<omega> \<in> space (kernel_source (K 0))" "A' \<in> sets (PiM {0..Suc n} (\<lambda>n. kernel_target (K n)))"
  shows "PiK (Suc n) K \<omega> A' = (\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (Suc n:=\<omega>)) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) \<omega>)"
  using assms apply (simp add: transition_kernel_PiK_Suc)
  using transition_kernel_PiK_Suc[OF assms(1-3)] by auto

locale stochastic_kernel_family =
  fixes K :: "nat \<Rightarrow> ('a, 'a) kernel"
  and n :: nat
assumes stochastic_kernels: "\<And>k. k \<le> n \<Longrightarrow> stochastic_kernel (K k)"
  and consistent_sets: "\<And>k. k < n \<Longrightarrow> kernel_target (K k) = kernel_source (K (Suc k))"
begin

lemma PiK_stochastic:
  shows "stochastic_kernel (PiK n K)"
  using stochastic_kernels consistent_sets
proof (induct n)
  case 0
  have "(\<lambda>x. \<lambda>n\<in>{0}. x) -` space (Pi\<^sub>M {0} (\<lambda>n. kernel_target (K n))) \<subseteq> space (kernel_target (K 0))"
    apply (subst space_PiM)
    by force
  then show ?case
    apply (intro stochastic_kernelI prob_spaceI)
    apply (subst kernel_measure_emeasure)
    apply (subst PiK_apply_0)
      apply (metis PiK_source)
    apply auto
    by (smt (verit, ccfv_SIG) "0" Int_absorb2 less_eq_nat.simps(1) restrict_PiE_iff singletonD 
        space_PiM stochastic_kernel.kernel_space_eq_1 subset_antisym subset_vimage_iff)
next
  case (Suc n)
  show ?case
    apply (intro stochastic_kernelI prob_spaceI)
    apply (subst kernel_measure_emeasure)
    apply (subst PiK_apply_Suc)
    using Suc stochastic_kernel_def apply auto[1]
        apply (simp add: Suc.prems stochastic_kernel.axioms(1))
    using Suc.prems(2) apply blast
    apply (simp_all add: space_PiM)
    apply (subst nn_integral_cong[where v="(\<lambda>_. 1)"])
     apply auto
     apply (subst nn_integral_cong[where v="(\<lambda>_.1)"])
     apply auto
    unfolding indicator_def apply (auto simp: space_PiM)
    apply (metis PiE_iff atLeast0AtMost atMost_iff le_SucE)
    using PiE_arb apply fastforce
    apply (simp add: PiE_iff Suc.prems stochastic_kernel.kernel_space_eq_1)
    by (metis Suc PiK_source PiK_target le_SucI less_SucI space_PiM stochastic_kernel.kernel_space_eq_1)
qed

end

locale stochastic_family_measure = K?: stochastic_kernel_family K + M?: prob_space M
  for K :: "nat \<Rightarrow> ('a, 'a) kernel" and M :: "'a measure" +
  assumes sets_eq_measure: "sets (kernel_source (K 0)) = sets M"
      and nonempty: "space M \<noteq> {}"

sublocale stochastic_family_measure \<subseteq> finite_measure_kernel "PiK n K"
  apply (intro finite_measure_kernel.intro)
    apply (rule stochastic_kernel.axioms(1))
    apply (rule PiK_stochastic)
   apply simp
  unfolding finite_measure_kernel_axioms_def using sets_eq_measure nonempty by simp

context stochastic_family_measure begin

definition PiK_semidirect_product where
"PiK_semidirect_product i \<equiv> distr (M \<Otimes>\<^sub>S PiK n K) (PiM (insert i ( {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))
   ((\<lambda>(x, y). y(i := x)))"

lemma measurable_insert_PiK [measurable]:
  assumes "i \<notin>  {0..n}"
  shows "(\<lambda>(x, y). y(i := x)) \<in> (M \<Otimes>\<^sub>S PiK n K) \<rightarrow>\<^sub>M
   (PiM (insert i {0..n}) ((\<lambda>i. kernel_target (K i))(i := M)))"
  using sets_kernel_semidirect_product apply measurable
   apply simp
   apply (subst(2) PiM_cong[where J="{0..n}" and N= "\<lambda>k. kernel_target (K k)"])
     apply blast
  using assms apply auto[1]
  apply (fact measurable_id)
   apply (simp add: kernel_semidirect_product_measurable)
  done

lemma PiK_semidirect_product_space [simp]:
  "space (PiK_semidirect_product i) = 
   space (PiM (insert i ( {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))"
  unfolding PiK_semidirect_product_def by simp

lemma PiK_semidirect_product_sets [simp]:
  "sets (PiK_semidirect_product i) = 
   sets (PiM (insert i {0..n}) ((\<lambda>i. kernel_target (K i))(i := M)))"
  unfolding PiK_semidirect_product_def by simp

lemma PiK_semidirect_product_emeasure:
  assumes [simp]: "A \<in> sets (PiK_semidirect_product i)" "i \<notin> {0..n}"
  shows "emeasure (PiK_semidirect_product i) A 
    = \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>2(i:=\<omega>\<^sub>1)) \<partial>kernel_measure (PiK n K) \<omega>\<^sub>1 \<partial>M"
  unfolding PiK_semidirect_product_def
  apply (subst emeasure_distr)
  using assms(2) measurable_insert_PiK apply blast
  using assms(1) apply simp
  apply (subst emeasure_semidirect_product)
  using measurable_insert_PiK[OF assms(2)] apply measurable
  using assms(1) PiK_semidirect_product_sets apply blast
  apply (rule nn_integral_cong)
  apply (rule nn_integral_cong)
  using assms apply simp
  by (smt (verit) case_prod_conv indicator_inter_arith indicator_simps(1) indicator_vimage 
      kernel_measure_space mem_Sigma_iff mult.right_neutral sets_eq_imp_space_eq
      sets_kernel_semidirect_product space_pair_measure)
end
text \<open> Klenke theorem 14.31 \<close>
lemma add_sets_borel[measurable]:
  fixes x :: "'a :: real_normed_vector"
  shows "A' \<in> sets borel \<Longrightarrow> {a. a + x \<in> A'} \<in> sets borel"
    apply measurable
    apply (rule pred_sets2[where N=borel])
    apply blast
    using borel_measurable_const_add[of id borel x] apply (simp add: add.commute measurable_ident)
    done

lemma (in prob_space) conv_distr_kernel:
  assumes [measurable]: "X \<in> borel_measurable M"
  shows "transition_kernel borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel X)) A')"
  apply (intro transition_kernel.intro)
     apply (subst convolution_emeasure)
             apply auto[1]
       apply (simp add: prob_space_return[THEN prob_space.finite_measure])
      apply measurable
    apply (rule finite_measure_distr)
  apply simp_all
     apply (subst nn_integral_return)
       apply simp
      apply simp
      apply (subst emeasure_distr)
      apply simp
  apply simp
      apply measurable
       apply (rule pred_sets2[where N=borel])
        apply blast
     apply measurable
      apply (subst emeasure_distr)
    apply simp
    apply (simp add: add_sets_borel)
      apply measurable
       apply (rule pred_sets2[where N=borel])
        apply blast
    apply measurable
    by (metis measure_space sets_convolution space_borel space_convolution)

lemma (in prob_space) conv_distr_kernel_stochastic:
  assumes [simp]: "random_variable borel X"
  shows "stochastic_kernel (kernel_of borel borel (\<lambda>x. emeasure (return borel x \<star> distr M borel X)))"
  apply (intro stochastic_kernelI prob_spaceI)
  apply simp
  apply (subst kernel_apply_kernel_of)
     apply (simp_all add: conv_distr_kernel[OF assms])
  apply (simp add: convolution_emeasure finite_measure_distr emeasure_distr emeasure_space_1)
  done

primrec phi :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: ab_group_add) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"phi 0 X = (\<lambda>x\<in>{0}. X 0)" | 
"phi (Suc n) X = (phi n X)(Suc n := sum X {0..Suc n})"

lemma phi_index [simp]: "k \<le> n \<Longrightarrow> phi n X k = sum X {0..k}"
  by (induct n arbitrary: k; simp)

lemma phi_notin[simp]: "ix \<notin> {0..n} \<Longrightarrow> phi n X ix = undefined"
  by (induct n; simp)

lemma phi_extensional[simp]: "phi n x \<in> extensional {0..n}"
  by (simp add: extensional_def)

lemma phi_restrict_arg: "phi n x ix = phi n (restrict x {0..n}) ix"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  consider "ix = Suc n" | "ix \<in> {0..n}" | "ix \<notin> {0..Suc n}"
    using le_SucE by fastforce
  then show ?case
    by (cases; simp add: Suc)
qed

corollary phi_restrict: "phi n x = phi n (restrict x {0..n})"
  using phi_restrict_arg by fast

lemma phi_cong:
  assumes "\<And>x. x \<in> {0..n} \<Longrightarrow> f x = g x"
  shows "phi n f = phi n g"
  using assms by (induct n, auto)

lemma phi_cong':
  assumes "\<And>x. x \<in> {0..n} \<Longrightarrow> f x = g x"
  shows "phi n f x = phi n g x"
  using assms by (induct n, auto)

lemma phi_measurable[measurable]:
  shows "phi n \<in> PiM {0..n} (\<lambda>_. borel) \<rightarrow>\<^sub>M PiM {0..n} (\<lambda>_. borel :: ('b :: ordered_euclidean_space) measure)"
proof (induct n)
  case 0
  then show ?case
    apply simp
   apply (rule measurable_PiM_single)
    apply (smt (verit, best) PiE_I Pi_I UNIV_I singleton_iff space_borel)
    apply auto[1]
    done
next
  case (Suc n)
  have phi_eq_comp: "phi (Suc n) = 
  (\<lambda>(x,y). (phi n x)(Suc n := sum x {0..n} + y)) \<circ> (\<lambda>x. (restrict x {0..n}, x (Suc n)))"
    by (auto simp add: fun_eq_iff atLeast0_atMost_Suc intro!: phi_restrict_arg)
  then show ?case
    apply (subst phi_eq_comp)
    apply (rule measurable_comp[where N="Pi\<^sub>M {0..n} (\<lambda>_. borel) \<Otimes>\<^sub>M borel"])
     apply measurable
    apply (simp add: atLeast0_atMost_Suc)
    apply measurable
    using Suc measurable_fst'' apply blast
    by force
qed

primrec phi_inv :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: ab_group_add) \<Rightarrow> (nat \<Rightarrow> 'a)" where
"phi_inv 0 X = (\<lambda>x\<in>{0}. X 0)" |
"phi_inv (Suc n) X = (phi_inv n X)(Suc n := (X (Suc n) - X n))"

lemma phi_inv_notin[simp]: "ix \<notin> {0..n} \<Longrightarrow> phi_inv n X ix = undefined"
  by (induct n; simp)

lemma phi_inv_Suc_index[simp]: "k < n \<Longrightarrow> phi_inv n X (Suc k) = X (Suc k) - X k"
  by (induct n arbitrary: k; simp)

lemma phi_inv_zero_index[simp]: "phi_inv n X 0 = X 0"
  by (induct n; simp) 

lemma phi_inv_restrict: "phi_inv n X ix = phi_inv n (restrict X {0..n}) ix"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  consider (zero) "ix = 0" | (nonzero) "ix \<in> {1..Suc n}" | (notin) "ix \<notin> {0..Suc n}"
    using le_SucE by fastforce
  then show ?case
  proof cases
    case zero
    then show ?thesis by simp
  next
    case nonzero
    then obtain ix' where "ix = Suc ix'" "ix' \<le> n"
      by (metis One_nat_def atLeastAtMost_iff not0_implies_Suc not_less_eq_eq zero_order(1))
    then show ?thesis
      by simp
  next
    case notin
    then show ?thesis by simp
  qed
qed

lemma phi_inv_phi_cancel: "x \<in> {0..n} \<rightarrow>\<^sub>E UNIV \<Longrightarrow> phi_inv n (phi n x) k = x k"
proof (induct k arbitrary: n)
  case 0
  show ?case
    by auto
next
  case (Suc k)
  consider "k < n" | "k \<ge> n"
    by linarith
  then show "phi_inv n (phi n x) (Suc k) = x (Suc k)"
    by (cases; simp; metis PiE_arb Suc.prems atLeastAtMost_iff not_less_eq_eq)
qed

lemma phi_phi_inv_cancel: "x \<in> {0..n} \<rightarrow>\<^sub>E UNIV \<Longrightarrow> phi n (phi_inv n x) k = x k" for k
proof (induct k arbitrary: n)
  case 0
  show ?case
    by auto
next
  case (Suc k)
  consider "k < n" | "k \<ge> n"
    by linarith
  then show "phi n (phi_inv n x) (Suc k) = x (Suc k)"
    apply cases
     apply simp
     apply (metis Suc order_le_less phi_index)
    by (metis PiE_arb Suc.prems atLeastAtMost_iff not_less_eq_eq phi_notin)
qed

lemma phi_bij_betw: "bij_betw (phi n) ({0..n} \<rightarrow>\<^sub>E UNIV) ({0..n} \<rightarrow>\<^sub>E UNIV)"
  apply (intro bij_betwI[where g="phi_inv n"])
    apply (induct n;intro Pi_I PiE_I; simp add: phi_notin)+
  using phi_inv_phi_cancel phi_phi_inv_cancel apply blast+
  done

corollary phi_inj_on [simp]: "inj_on (phi n) ({0..n} \<rightarrow>\<^sub>E UNIV)"
  using phi_bij_betw bij_betw_def by blast

lemma phi_inv_into: "i \<in> {0..n} \<rightarrow>\<^sub>E UNIV \<Longrightarrow> phi_inv n i = inv_into ({0..n} \<rightarrow>\<^sub>E UNIV) (phi n) i"
  apply (rule inv_into_f_eq[symmetric])
  using bij_betw_imp_inj_on phi_bij_betw apply blast
   apply auto[1]
  using phi_phi_inv_cancel by blast

lemma phi_the_inv_into: "i \<in> {0..n} \<rightarrow>\<^sub>E UNIV \<Longrightarrow> the_inv_into ({0..n} \<rightarrow>\<^sub>E UNIV) (phi n) i = phi_inv n i"
  apply (simp add: the_inv_into_def)
  apply (rule the_equality)
   apply (smt (verit, del_insts) PiE_I PiE_ext UNIV_I phi_inv_notin phi_phi_inv_cancel)
  by (metis bij_betw_inv_into_left phi_bij_betw phi_inv_into)

lemma phi_inv_into_image: "S \<subseteq> {0..n} \<rightarrow>\<^sub>E UNIV \<Longrightarrow> phi_inv n ` S = inv_into ({0..n} \<rightarrow>\<^sub>E UNIV) (phi n) ` S"
  using refl phi_inv_into by (rule image_cong, blast)

corollary phi_range: "(phi n) ` ({0..n} \<rightarrow>\<^sub>E UNIV) = ({0..n} \<rightarrow>\<^sub>E UNIV)"
  using bij_betw_imp_surj_on[OF phi_bij_betw] by metis

lemma phi_inv_range: "(phi_inv n) ` ({0..n} \<rightarrow>\<^sub>E UNIV) = ({0..n} \<rightarrow>\<^sub>E UNIV)"
  by (metis PiE_mono inv_into_image_cancel phi_inj_on phi_inv_into_image phi_range top_greatest)

lemma sum_measurable_PiM[measurable]:
  "(\<lambda>x. \<Sum>i\<in>S. x i) \<in> borel_measurable (PiM S 
  (\<lambda>_. borel :: ('b:: {second_countable_topology,topological_comm_monoid_add} measure)))"
  apply (rule borel_measurable_sum)
  by simp

lemma phi_inv_measurable[measurable]:
  shows "phi_inv n \<in> PiM {0..n} (\<lambda>_. borel) \<rightarrow>\<^sub>M PiM {0..n} (\<lambda>_. borel :: ('b :: ordered_euclidean_space) measure)"
proof (induct n)
  case 0
  then show ?case
    apply simp
   apply (rule measurable_PiM_single)
    apply (smt (verit, best) PiE_I Pi_I UNIV_I singleton_iff space_borel)
    apply auto[1]
    done
next
  case (Suc n)
  have phi_eq_comp: "phi_inv (Suc n) = 
  (\<lambda>(x,y). (phi_inv n x)(Suc n := y - x n)) \<circ> (\<lambda>x. (restrict x {0..n}, x (Suc n)))"
    using phi_inv_restrict fun_eq_iff atLeast0_atMost_Suc by fastforce    
  then show ?case
    apply (subst phi_eq_comp)
    apply (rule measurable_comp[where N="Pi\<^sub>M {0..n} (\<lambda>_. borel) \<Otimes>\<^sub>M borel"])
     apply measurable
    apply (simp add: atLeast0_atMost_Suc)
    apply measurable
    using Suc measurable_fst'' apply blast
    by force
qed

lemma phi_measurable_isomorphic [simp]:
  "measurable_isomorphic_map (PiM {0..n} (\<lambda>_. borel :: ('b :: ordered_euclidean_space) measure))
   (PiM {0..n} (\<lambda>_. borel)) (phi n)"
  apply (intro measurable_isomorphic_mapI)
    apply (simp add: space_PiM phi_bij_betw)
   apply (fact phi_measurable)
  apply (subst measurable_cong[where g="phi_inv n"])
   apply (simp add: space_PiM phi_the_inv_into)
  apply measurable
  done

corollary phi_image_sets[measurable]:
  fixes A :: "(nat \<Rightarrow> 'a :: ordered_euclidean_space) set"
  assumes "A \<in> PiM {0..n} (\<lambda>_. borel)"
  shows "phi n ` A \<in> PiM {0..n} (\<lambda>_. borel)"
  using assms by (fact phi_measurable_isomorphic[THEN measurable_isomorphic_mapD'(1)])

lemma PiM_borel_phi:
  shows "sigma_sets ({0..n} \<rightarrow>\<^sub>E UNIV) ((`) (phi n) ` {Pi\<^sub>E {0..n} X |X. X \<in> {0..n} \<rightarrow> sets borel}) =
  sets (PiM {0..n::nat} (\<lambda>_. borel :: ('b :: ordered_euclidean_space) measure))"
  apply (simp only: space_PiM[symmetric] space_borel[symmetric])
  apply (rule measurable_isomorphic_map_sigma_sets[of "PiM {0..n::nat} (\<lambda>_. borel)", symmetric])
   apply (simp add: sets_PiM space_PiM)
   apply (rule arg_cong2[where f=sigma_sets])
    apply simp
   apply (simp add: prod_algebra_eq_finite)
  apply (fact phi_measurable_isomorphic)
  done

lemma phi_Suc_image_PiE: "phi (Suc n) ` (PiE {0..Suc n} A) = 
  (\<lambda>(y,x). x(Suc n := x n + y)) ` (A (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A)"
apply (intro subset_antisym subsetI)
  unfolding image_def apply auto[1]
   apply (rule_tac x="xa (Suc n)" in bexI)
    apply (rule_tac x="phi n (xa (Suc n := undefined))" in exI)
    apply auto[1]
     apply (rule_tac x="xa (Suc n:= undefined)" in bexI)
      apply (rule phi_cong)
      apply auto[1]
     apply (rule fun_upd_in_PiE)
      apply simp
  using atLeast0_atMost_Suc apply blast
    apply (rule arg_cong3[where g=fun_upd])
      apply (auto intro: phi_cong)[1]
     apply simp_all
   apply fastforce
  apply auto[1]
  apply (rule_tac x="xb(Suc n := xa)" in bexI)
   apply simp
   apply (rule arg_cong3[where g=fun_upd])
     apply (auto intro: phi_cong)[1]
    apply simp_all
  apply (rule PiE_I)
   apply fastforce
  unfolding fun_upd_def apply simp
  apply (rule PiE_arb[where S="{0..n}" and T="A"])
   apply auto
  done

lemma phi_Suc_image_PiE_vimage: "phi (Suc n) ` (PiE {0..Suc n} A) = 
  ((\<lambda>x. (x (Suc n) - x n, restrict x {0..n})) -` (A (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A))
   \<inter> ({0..Suc n} \<rightarrow>\<^sub>E UNIV)"
  apply (subst phi_Suc_image_PiE)
  unfolding image_def vimage_def apply safe
  apply simp_all
   apply force
  apply (rule_tac x="x (Suc n) - x n" in bexI)
   apply (rule_tac x="restrict x {0..n}" in exI)
   apply safe
   apply (rule_tac x=xa in bexI)
    apply simp_all
  apply (rule ext)
  apply auto
   apply (metis atLeastAtMost_iff le0 order.refl phi_index restrict_apply')
  apply (metis PiE_arb atLeast0_atMost_Suc insert_iff restrict_def)
  done

lemma Int_stable_inj_image[intro]:
  assumes "inj_on f (\<Union>S)" "Int_stable S"
  shows "Int_stable (((`) f) ` S)"
  by (rule Int_stableI_image, metis Int_stable_def Sup_upper assms inj_on_image_Int)  

lemma measurable_vimage_PiM_borel [simp]:
  "A \<in> sets (Pi\<^sub>M {i} (\<lambda>_. borel)) \<Longrightarrow> (\<lambda>x. \<lambda>n\<in>{i}. x) -` A \<in> sets borel"
  apply (rule measurable_sets_borel)
   prefer 2 apply blast
  apply measurable
  done

lemma the_inv_plus [simp]:
  fixes c :: "'a :: real_normed_vector"
  shows "the_inv ((+) c) = (\<lambda>x. x - c)"
  unfolding the_inv_into_def
  apply (rule ext)
  apply simp
  apply (rule the1_equality)
   apply (metis Groups.add_ac(2) cross3_simps(16))
  by simp

lemma borel_measurable_diff_const [measurable]:
  fixes c :: "'a :: {second_countable_topology,real_normed_vector}"
  shows "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. f x - c) \<in> borel_measurable M"
  using borel_measurable_diff[where g = "\<lambda>_. c"] by fastforce

lemma add_measurable_isomorphic_borel:
  fixes c :: "'b :: {second_countable_topology, real_normed_vector}"
  shows "measurable_isomorphic_map borel borel (\<lambda>x. c + x)"
  by (intro measurable_isomorphic_mapI; simp add: bij_plus_right)

corollary cadd_image_sets_borel[measurable]:
  fixes c :: "'b :: {second_countable_topology, real_normed_vector}"
  assumes "A \<in> sets borel"
  shows "(+) c ` A \<in> sets borel"
  by (fact measurable_isomorphic_mapD'(1)[OF add_measurable_isomorphic_borel assms])

lemma indicator_image_inj_on:
  assumes "inj_on f S" "x \<in> S" "A \<subseteq> S"
  shows "indicator (f ` A) (f x) = indicator A x"
  using assms by (simp add: inj_on_image_mem_iff split: split_indicator)

declare phi.simps [simp del]
declare PiK.simps [simp del]

text \<open> Klenke Theorem 14.31. \<close>

text \<open> TODO: Prove this without the index set, and use re-indexing with @{thm distr_PiM_reindex} to obtain
the full theorem \<close>

lemma indicator_image_phi_Suc:
  fixes A' :: "(nat \<Rightarrow> ('a :: ordered_euclidean_space) set)" and x a
  assumes [measurable]: "\<And>i. i \<in> {0..Suc n} \<Longrightarrow> A' i \<in> sets borel"
      and x: "x \<in> {0..n} \<rightarrow>\<^sub>E UNIV"
  shows "(indicator (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') (x(Suc n := a)) :: ennreal) =
  indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator ((+) (x n) ` A' (Suc n)) a"
proof -
  have 1: "(phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') =
     (\<lambda>(y, x). x(Suc n := x n + y)) ` (A' (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A')"
    by (fact phi_Suc_image_PiE)
  have 2: "x(Suc n := a) = (\<lambda>(y, x). x(Suc n := x n + y)) (a - x n, x)"
    by simp
  have "(indicator (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') (x(Suc n := a)) :: ennreal) =
  indicator (A' (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A') (a - x n, x)"
    apply (simp only: 1 2)
    apply (subst indicator_image_inj_on[where S="UNIV \<times> ({0..n} \<rightarrow>\<^sub>E UNIV)"])
     apply (rule inj_onI)
    apply safe
           apply (metis add_left_cancel fun_upd_eqD fun_upd_triv fun_upd_twist n_not_Suc_n)
          apply simp_all
     apply (rule ext)
     apply (case_tac "x \<in> {0..n}")
      apply (metis array_rules(4) atLeastAtMost_iff le_antisym lessI less_or_eq_imp_le n_not_Suc_n)
     apply fastforce
    using x apply auto
    done
  also have "... = indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator (A' (Suc n)) (a - x n)"
    by (simp add: indicator_times[of "A' (Suc n)" "phi n ` Pi\<^sub>E {0..n} A'" "(a - x n, x)"] field_simps)
  also have "... = indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator ((+) (x n) ` A' (Suc n)) a"
    apply (auto intro!: arg_cong2[where f="(*)"])
    unfolding indicator_def apply auto
    by (simp add: rev_image_eqI)
  finally show ?thesis .
qed


(*(1,2,3) \<rightarrow>\<^sub>\<phi> (1,3,6) *)
(*X = id \<Longrightarrow> S 1 1 = 1, S 2 2 = 4, S 3 3 = 9 *)
(* X (1,2,3) = f S (1,3,6) *)
lemma (in prob_space) PiM_S_phi:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> ('b :: ordered_euclidean_space)"
  assumes [measurable]: "\<And>i. X i \<in> borel_measurable M" "A' \<in> {0..n} \<rightarrow> sets borel"
      and "indep_vars (\<lambda>_. borel) X {0..n}"
  defines "S \<equiv> (\<lambda>k \<omega>. \<Sum>j \<in> {0..k}. X j \<omega>)"
  shows "(\<Pi>\<^sub>M t \<in> {0..n}. distr M borel (S t)) (phi n ` (Pi\<^sub>E {0..n} A')) =
          (\<Prod>t \<in> {0..n}. distr M borel (X t) (A' t))"
  using assms(2,3)
proof (induct n arbitrary: A')
  case 0
  then show ?case
    apply simp
    sorry
next
  case (Suc n)
  then have [measurable]: "A' k \<in> sets borel" if "k \<in> {0..Suc n}" for k
    using that by blast
  have indep_X_S: "indep_var borel (X (Suc n)) borel (S n)"
    unfolding S_def using Suc(3) by (auto intro!: indep_vars_sum' simp: atLeast0_atMost_Suc)
  have "emeasure (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (S t))) (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') =
    emeasure (distr ((distr M borel (S (Suc n))) \<Otimes>\<^sub>M Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)))
      (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (S t))) (\<lambda>(x, X). X(Suc n := x))) (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A')"
    apply (rule arg_cong2[where f=emeasure])
     apply (simp add: atLeast0_atMost_Suc)
     apply (rule distr_pair_PiM_eq_PiM[of "{0..n}" "(\<lambda>t. distr M borel (S t))" "Suc n", symmetric])
      apply (simp_all add: assms(4) prob_space_distr)
    done
  also have "... = emeasure (distr M borel (S (Suc n)) \<Otimes>\<^sub>M Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)))
     ((\<lambda>(x, X). X(Suc n := x)) -` phi (Suc n) ` Pi\<^sub>E {0..Suc n} A' \<inter> UNIV \<times> ({0..n} \<rightarrow>\<^sub>E UNIV))"
    apply (subst emeasure_distr)
     apply (simp add: atLeast0_atMost_Suc)
     apply measurable
    apply (simp add: space_pair_measure space_PiM)
    done
  also have "... = emeasure (distr M borel (S (Suc n)) \<Otimes>\<^sub>M Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)))
    {(sum x {0..Suc n}, phi n x) | x. x \<in> Pi\<^sub>E {0..Suc n} A'}"
  proof (intro arg_cong2[where f=emeasure] refl set_eqI iffI, goal_cases L R)
    case (L x)
    then show ?case
     apply auto
     apply (rule_tac x=xaa in exI)
     apply safe
      apply (metis fun_upd_same le_Suc_eq phi_index sum.atLeast0_atMost_Suc)
      apply (simp add: phi.simps)
      apply (rule ext)
      apply (case_tac "xb \<in> {0..n}")
       apply (metis Suc_n_not_le_n atLeastAtMost_iff fun_upd_other)
      apply auto
      done
  next
    case (R x)
    then show ?case
      apply auto
      by (metis image_iff phi.simps(2) sum.atLeast0_atMost_Suc)
  qed
  also have "... =  \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.
   indicator {(sum x {0..Suc n}, phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'} (x, y)
   \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>distr M borel (S (Suc n))"
    apply (rule sigma_finite_measure.emeasure_pair_measure)
    sorry
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+ y.
   indicator {(x (Suc n), phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'} (x, y)
   \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>distr M borel (X (Suc n))"
  proof -
    have 1: "S (Suc n) = (\<lambda>\<omega>. S n \<omega> + X (Suc n) \<omega>)"
      unfolding S_def by fastforce
    then have "distr M borel (S (Suc n)) = (distr M borel (S n) \<star> distr M borel (X (Suc n)))"
      apply (auto intro!: sum_indep_random_variable)
      using indep_var_sym indep_X_S indep_var_rv2 apply blast+
      done
    then have "\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. indicator {(sum x {0..Suc n}, phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'}
       (x, y) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>distr M borel (S (Suc n)) =
      \<integral>\<^sup>+ xa. \<integral>\<^sup>+xb. \<integral>\<^sup>+ y. indicator {(sum x {0..Suc n}, phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'}
       ((xa + xb), y) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>distr M borel (X (Suc n)) \<partial>distr M borel (S n)"
      apply simp
      apply (rule nn_integral_convolution)
          prefer 5
      apply (rule sigma_finite_measure.borel_measurable_nn_integral)
           defer
      apply (subst case_prod_eta)
           apply (rule borel_measurable_indicator)
           apply measurable
      sorry (* Measurable goals *)
    also have "... = \<integral>\<^sup>+ xa. \<integral>\<^sup>+xb. \<integral>\<^sup>+ y. indicator {(sum x {0..Suc n}, phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'}
       ((S n xa + xb), y) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>distr M borel (X (Suc n)) \<partial>M"
      apply (rule nn_integral_distr)
      unfolding S_def apply measurable
      sorry
    also have "... = \<integral>\<^sup>+ xa. \<integral>\<^sup>+xb. \<integral>\<^sup>+ y. indicator {(sum x {0..Suc n}, phi n x) |x. x \<in> Pi\<^sub>E {0..Suc n} A'}
       ((S n xa + X (Suc n) xb), y) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)) \<partial>M \<partial>M"
      apply (rule nn_integral_cong)
      apply (rule nn_integral_distr)
       apply measurable
      sorry
    finally show ?thesis
      apply (subst nn_integral_distr)
        prefer 3
        apply (subst nn_integral_distr)
          prefer 3
          apply (rule nn_integral_cong)+
          apply (simp split: split_indicator)
          apply safe
           apply (rule_tac x="xb(Suc n:= X (Suc n) x)" in exI)
           apply simp
           apply safe
             defer
      sorry
  qed 
  also have "... = (\<Prod>t = 0..Suc n. emeasure (distr M borel (X t)) (A' t))"
    sorry
  finally show ?case .
qed

(* xya(2)[THEN
qed
  have "emeasure (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (S t))) (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') =
      (\<integral>\<^sup>+\<omega>\<^sub>f. \<integral>\<^sup>+\<omega>. indicator (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') (\<omega>\<^sub>f(Suc n := \<omega>))
        \<partial>distr M borel (S (Suc n)) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)))"
    apply (subst nn_integral_indicator[symmetric])
     apply measurable
    apply (subst atLeast0_atMost_Suc)
    apply (subst product_sigma_finite.product_nn_integral_insert)
        apply (auto intro!: product_sigma_finite.intro prob_space_imp_sigma_finite simp: prob_space_distr S_def)[1]
       apply simp_all
     apply measurable
    using atLeast0_atMost_Suc apply simp
    done

  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. \<integral>\<^sup>+ \<omega>. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f 
      * indicator ((+) (\<omega>\<^sub>f n) ` A' (Suc n)) \<omega>
     \<partial>distr M borel (S (Suc n)) \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t))"
    apply (intro nn_integral_cong)
    apply (subst indicator_image_phi_Suc)
      apply (simp_all add: space_PiM)
    done

  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. distr M borel (S (Suc n)) ((+) (\<omega>\<^sub>f n) ` A' (Suc n)) * indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f
      \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t))"
    apply (rule nn_integral_cong)
    apply (subst(2) mult.commute)
    apply (subst nn_integral_cmult)
     apply measurable[1]
    by simp
  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. distr M borel (X (Suc n)) (A' (Suc n)) * indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f 
      \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t))"
  proof (rule set_nn_integral_cong; simp)
    fix \<omega>\<^sub>f assume "\<omega>\<^sub>f \<in> phi n ` Pi\<^sub>E {0..n} A'"
    have "measure (distr M borel (S (Suc n))) ((+) (\<omega>\<^sub>f n) ` A' (Suc n)) = 
          prob ((\<lambda>\<omega>. (\<Sum>j = 0..n. X j \<omega>) + X (Suc n) \<omega>) -` (+) (\<omega>\<^sub>f n) ` A' (Suc n) \<inter> space M)"
      unfolding S_def by (simp add: measure_distr)
    also have "... = undefined"
    sorry
  also have "... = distr M borel (X (Suc n)) (A' (Suc n)) *
    (\<integral>\<^sup>+ \<omega>\<^sub>f. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f \<partial>Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (S t)))"
    by (simp add: nn_integral_cmult)
  also have "... = distr M borel (X (Suc n)) (A' (Suc n)) * Pi\<^sub>M {0..n} (\<lambda>t. distr M borel (X t)) (Pi\<^sub>E {0..n} A')"
    apply (subst Suc(1)[symmetric])
      apply simp
    using Suc(3) apply (meson atLeastatMost_subset_iff indep_vars_subset lessI less_or_eq_imp_le)
    by simp
  also have "... = (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (X t))) (Pi\<^sub>E {0..Suc n} A')"
    by (simp add: emeasure_PiM_Suc prob_space_distr
          prob_space_imp_sigma_finite product_sigma_finite.intro)
  finally show ?case .
qed*)

(*lemma assumes "A' \<in> {0,1} \<rightarrow> sets borel"
shows "X 0 x + X (Suc 0) x =
       xa 0 + xa (Suc 0) \<Longrightarrow>
       xa \<in> Pi\<^sub>E {0..Suc 0} A' \<Longrightarrow>
       X (Suc 0) x \<in> A' (Suc 0)"

X : {0,1} -> 'a (x) -> 'b (xa)
x : 'a
X 0 x = 2
X 1 x = 5

xa 0 = 3
xa 1 = 4

X 0 x + X 1 x = xa 0 + xa 1

A' 0 = {3..4}
A' 1 = {3..4}

xa : {0,1} -> 'b
A' : {0,1} -> 'b set
*)

theorem (in prob_space) pair_kernel_convolution:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> ('b :: ordered_euclidean_space)"
  assumes "indep_vars (\<lambda>_. borel) X {0..(n::nat)}"
      and [measurable]: "\<And>i. random_variable borel (X i)"
  defines "S \<equiv> (\<lambda>k \<omega>. \<Sum>j \<in> {0..k}. X j \<omega>)"
    and "K \<equiv> (\<lambda>k. kernel_of borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel (X k))) A'))"
  shows "kernel_measure (PiK n K) 0 = (\<Pi>\<^sub>M t\<in>{0..n}. distr M borel (S t))"
  using assms(1)
proof (induct n)
  case 0
  have target_K [simp]: "kernel_target (K n) = borel" for n
    unfolding K_def by simp
  have measurable_S[measurable]: "\<And>i. random_variable borel (S i)"
    unfolding S_def by measurable
  show ?case
    apply (rule measure_eqI_generator_eq
          [where E="{PiE {0} A | A. A 0 \<in> sets borel}" and \<Omega>="{0} \<rightarrow>\<^sub>E UNIV" and A = "\<lambda>_. {0} \<rightarrow>\<^sub>E UNIV"])
    using Int_stable_PiE[of "{0}" "{0}" "\<lambda>_. borel"]
           apply auto[1]
          apply blast
    defer
         apply (simp add: K_def sets_PiM_single)
         apply (auto intro!: arg_cong2[where f=sigma_sets] simp: PiE_def)[1]
        apply (simp add: sets_PiM_single PiE_def)
        apply (auto intro!: arg_cong2[where f=sigma_sets])[1]
       apply auto[1]
      apply simp
    using stochastic_kernel_family.PiK_stochastic[
        THEN stochastic_kernel.kernel_measure_emeasure_finite, of K 0 0]
     apply (simp add: space_PiM)
    using stochastic_kernel_family.intro[of 0 K] K_def conv_distr_kernel_stochastic
     apply (metis assms(2) less_zeroE)
    apply simp
    apply (erule exE)
    apply simp
    apply (subst finite_product_sigma_finite.measure_times)
      apply (intro finite_product_sigma_finite.intro product_sigma_finite.intro)
    using measurable_S[THEN prob_space_distr] prob_space_imp_sigma_finite apply blast
      apply (meson finite.intros finite_product_sigma_finite_axioms.intro)
     apply simp
    unfolding K_def apply (simp add: PiK.simps)
    apply (subst(2) kernel_apply_kernel_of)
       apply simp
      apply (metis finite.emptyI finite.insertI sets_PiM_I_finite singletonD)
        apply (rule transition_kernel.intro)
         apply (subst kernel_apply_kernel_of)
            apply auto
          apply (simp add: conv_distr_kernel)
         apply (subst convolution_emeasure)
                apply simp_all
        using prob_space.finite_measure prob_space_distr assms(2) apply blast
         apply (subst nn_integral_return)
           apply (simp_all add: emeasure_distr)
        unfolding measure_space_def
        apply safe
          apply (rule sets.sigma_algebra_axioms)
        unfolding positive_def apply auto
        apply (rule countably_additive_image'[OF kernel.countably_additive, where S="\<lambda>x. (\<lambda>i\<in>{0}. x)"])
           apply simp_all
          apply (rule inj_on_subset[where A=UNIV])
           apply (metis (mono_tags, lifting) empty_Collect_eq ex_in_conv injI insert_compr restrict_apply')
          apply simp
         apply (simp add: sets_PiM_single_image')
        apply simp
        unfolding inv_def image_def vimage_def
        apply (rule Collect_cong)
        apply safe
         apply (rule_tac x="(\<lambda>i\<in>{0}. x)" in bexI)
          apply (subst some1_equality)
            apply auto
         apply (metis empty_not_insert equals0I restrict_apply')
        apply (simp add: sets_PiM_single_image)
        apply (erule imageE)
        apply (simp add: image_iff)
        apply (erule bexE)
        apply (rule_tac x="xb" in bexI)
         apply (rule restrict_cong)
          apply blast
         apply auto[1]
        unfolding simp_implies_def apply (rule some_equality)
          apply simp
         apply (metis ex_in_conv insert_not_empty restrict_apply')
         apply simp
        apply (subst kernel_apply_kernel_of)
           apply auto
        using assms(2) conv_distr_kernel apply blast
        apply (subst convolution_emeasure)
               apply auto
        using assms(2) finite_measure_distr apply blast
        apply (subst emeasure_distr)
          apply auto
        apply (subst nn_integral_return)
        apply (auto simp: S_def)
        done
next
  case (Suc n)
    have [simp]: "transition_kernel borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel (X k))) A')" for k
      using assms(2) conv_distr_kernel by blast
    then have K_apply: "K k \<omega> A' = ((return borel \<omega>) \<star> (distr M borel (X k))) A'"
      if "k \<in> {0..Suc n}" "A' \<in> sets borel" for k A' \<omega>
      unfolding K_def using that by simp
    have indep_X_S: "indep_var borel (X (Suc n)) borel (S n)"
      unfolding S_def using Suc(2) by (auto intro!: indep_vars_sum' simp: atLeast0_atMost_Suc)
    have "\<And>k. k \<in> {0..Suc n} \<Longrightarrow> stochastic_kernel (K k)"
      apply (intro stochastic_kernel_altI)
      apply (subst K_apply; simp add: K_def)
      apply (subst convolution_emeasure)
             apply auto
       apply (rule finite_measure_distr)
      apply simp
      by (metis prob_space_distr[OF assms(2)] prob_space.emeasure_space_1 space_borel space_distr)
    then interpret stochastic_kernel_family K "Suc n"
      unfolding K_def by (simp add: stochastic_kernel_family.intro)
  let ?E = "((`) (phi (Suc n)) ` {Pi\<^sub>E {0..(Suc n)} X |X. X \<in> {0..(Suc n)} \<rightarrow> sets (borel :: ('b :: ordered_euclidean_space) measure)})"
  (* Suffices to show equality on ?E, since it generates the borel sets. *)
  show ?case
  proof (rule measure_eqI_generator_eq[where E="?E" and \<Omega>="{0..Suc n} \<rightarrow>\<^sub>E UNIV"])
    show "Int_stable ((`) (phi (Suc n)) ` {Pi\<^sub>E {0..(Suc n)} X |X. X \<in> {0..Suc n} \<rightarrow> sets borel})"
      apply (rule Int_stable_inj_image)
       apply (blast intro: inj_on_subset phi_bij_betw[THEN bij_betw_imp_inj_on])
      apply (safe intro!: Int_stableI)
      apply (smt (verit, ccfv_threshold) PiE_Int Pi_iff sets.Int)
      done
    show "(`) (phi (Suc n)) ` {Pi\<^sub>E {0..Suc n} X |X. X \<in> {0..Suc n} \<rightarrow> sets borel} \<subseteq> Pow ({0..Suc n} \<rightarrow>\<^sub>E UNIV)"
      by auto
    show "sets (kernel_measure (PiK (Suc n) K) 0) =
    sigma_sets ({0..Suc n} \<rightarrow>\<^sub>E UNIV) ((`) (phi (Suc n)) ` {Pi\<^sub>E {0..Suc n} X |X. X \<in> {0..Suc n} \<rightarrow> sets borel})"
      by (subst PiM_borel_phi, auto simp: K_def)
    show "sets (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (S t))) =
    sigma_sets ({0..Suc n} \<rightarrow>\<^sub>E UNIV) ((`) (phi (Suc n)) ` {Pi\<^sub>E {0..Suc n} X |X. X \<in> {0..Suc n} \<rightarrow> sets borel})"
      by (subst PiM_borel_phi, auto cong: sets_PiM_cong)
    show "range (\<lambda>_. {0..Suc n} \<rightarrow>\<^sub>E UNIV) \<subseteq> (`) (phi (Suc n)) ` {Pi\<^sub>E {0..Suc n} X |X. X \<in> {0..Suc n} \<rightarrow> sets borel}"
      by (auto intro!: rev_image_eqI[where x="{0..Suc n} \<rightarrow>\<^sub>E UNIV"] simp: phi_range)
    show "(\<Union>i. {0..Suc n} \<rightarrow>\<^sub>E UNIV) = {0..Suc n} \<rightarrow>\<^sub>E UNIV"
      by simp
    show "\<And>i. emeasure (kernel_measure (PiK (Suc n) K) 0) ({0..Suc n} \<rightarrow>\<^sub>E UNIV) \<noteq> \<infinity>"
      using PiK_stochastic[THEN stochastic_kernel.kernel_space_eq_1]
      by (simp add: K_def space_PiM)

  next
    have K_image_plus: "K (Suc n) x (((+) x) ` A) = distr M borel (X (Suc n)) A"
      if [measurable]: "A \<in> sets borel" for x A
      apply (subst K_apply; simp)
      apply (subst convolution_emeasure)
      apply measurable
      using prob_space_distr[OF assms(2)] prob_space.axioms(1) apply blast
      apply simp_all
      apply (subst nn_integral_return)
        apply simp
       apply (subst emeasure_distr)
         apply simp
        apply measurable
      apply (rule arg_cong2[where f=emeasure])
       apply auto
      done

    fix A :: "(nat \<Rightarrow> 'b) set"
    assume A: "A \<in> (`) (phi (Suc n)) ` {Pi\<^sub>E {0..Suc n} a |a. a \<in> {0..Suc n} \<rightarrow> sets borel}"
    then obtain A' where A': "A = phi (Suc n) ` Pi\<^sub>E {0..Suc n} A'" "A' \<in> {0..Suc n} \<rightarrow> sets borel"
      by blast
    then have [measurable]: "A' (Suc n) \<in> sets borel"
      by auto
    have [measurable]: "A \<in> PiM {0..Suc n} (\<lambda>_. borel)"
      apply (subst A'(1))
      apply (rule measurable_isomorphic_mapD'(1)[OF phi_measurable_isomorphic])
      apply (rule sets_PiM_I_countable)
      using A'(2) apply auto
      done

    have "emeasure (kernel_measure (PiK (Suc n) K) 0) A = (\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A (\<omega>\<^sub>f (Suc n:=\<omega>)) \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n))
                \<partial>kernel_measure (PiK n K) 0)"
      apply (simp only: kernel_measure_emeasure)
      apply (subst PiK_apply_Suc)
           apply (smt (verit, ccfv_threshold) All_less_Suc consistent_sets le_trans less_or_eq_imp_le
          order_trans_rules(19) stochastic_kernel.axioms(1) stochastic_kernel_family.PiK_stochastic
          stochastic_kernel_family.intro stochastic_kernels)
          apply (simp add: stochastic_kernel.axioms(1) stochastic_kernels)
         apply (simp_all add: K_def)
      done

    also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. \<integral>\<^sup>+ \<omega>. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f * indicator ((+) (\<omega>\<^sub>f n) ` A' (Suc n)) \<omega>
       \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n) \<partial>kernel_measure (PiK n K) 0"
    proof (intro nn_integral_cong; simp add: A' K_def space_PiM)
      fix x :: "nat \<Rightarrow> 'b" and a
      assume x: "x \<in> {0..n} \<rightarrow>\<^sub>E UNIV"
      have 1: "(phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') =
         (\<lambda>(y, x). x(Suc n := x n + y)) ` (A' (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A')"
        by (fact phi_Suc_image_PiE)
      have 2: "x(Suc n := a) = (\<lambda>(y, x). x(Suc n := x n + y)) (a - x n, x)"
        by simp
      have "(indicator (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') (x(Suc n := a)) :: ennreal) =
      indicator (A' (Suc n) \<times> phi n ` Pi\<^sub>E {0..n} A') (a - x n, x)"
        apply (simp only: 1 2)
        apply (subst indicator_image_inj_on[where S="UNIV \<times> ({0..n} \<rightarrow>\<^sub>E UNIV)"])
         apply (rule inj_onI)
        apply safe
               apply (metis add_left_cancel fun_upd_eqD fun_upd_triv fun_upd_twist n_not_Suc_n)
              apply simp_all
         apply (rule ext)
         apply (case_tac "x \<in> {0..n}")
          apply (metis array_rules(4) atLeastAtMost_iff le_antisym lessI less_or_eq_imp_le n_not_Suc_n)
         apply fastforce
        using x apply auto
        done
      also have "... = indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator (A' (Suc n)) (a - x n)"
        by (simp add: indicator_times[of "A' (Suc n)" "phi n ` Pi\<^sub>E {0..n} A'" "(a - x n, x)"] field_simps)
      also have "... = indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator ((+) (x n) ` A' (Suc n)) a"
        apply (auto intro!: arg_cong2[where f="(*)"])
        unfolding indicator_def apply auto
        by (simp add: rev_image_eqI)
      finally show "(indicator (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A') (x(Suc n := a)) :: ennreal) =
  indicator (phi n ` Pi\<^sub>E {0..n} A') x * indicator ((+) (x n) ` A' (Suc n)) a" .
    qed

    also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f * \<integral>\<^sup>+ \<omega>. indicator ((+) (\<omega>\<^sub>f n) ` A' (Suc n)) \<omega>
       \<partial>kernel_measure (K (Suc n)) (\<omega>\<^sub>f n) \<partial>kernel_measure (PiK n K) 0"
      apply (rule nn_integral_cong)
      apply (simp add: space_PiM)
      apply (subst nn_integral_cmult)
       apply measurable
      using K_def apply simp_all
      done

    also have "... = \<integral>\<^sup>+ \<omega>\<^sub>f. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f * distr M borel (X (Suc n)) (A' (Suc n))
      \<partial>kernel_measure (PiK n K) 0"
      apply (rule nn_integral_cong)
      apply (rule arg_cong2[where f="(*)"])
       apply simp
      apply (subst nn_integral_indicator)
       apply measurable
       apply (simp add: K_def)
      apply (subst kernel_measure_emeasure)
      apply (rule K_image_plus)
      apply measurable
      done

    also have "... = (distr M borel (X (Suc n))) (A' (Suc n)) * 
      \<integral>\<^sup>+ \<omega>\<^sub>f. indicator (phi n ` Pi\<^sub>E {0..n} A') \<omega>\<^sub>f \<partial>kernel_measure (PiK n K) 0"
    proof (subst nn_integral_multc)
      show "indicator (phi n ` Pi\<^sub>E {0..n} A') \<in> borel_measurable (kernel_measure (PiK n K) 0)"
        apply (rule borel_measurable_indicator)
        apply measurable
        apply (simp add: K_def)
         apply (rule measurable_isomorphic_mapD'(1)[OF phi_measurable_isomorphic])
         apply (rule sets_PiM_I_countable)
          apply auto
        using A'(2) apply auto
        done
    qed (fact mult.commute)
    also have "... = (distr M borel (X (Suc n))) (A' (Suc n)) *
                     (\<Pi>\<^sub>M t \<in> {0..n}. distr M borel (S t)) (phi n ` (Pi\<^sub>E {0..n} A'))"
      apply (rule arg_cong2[where f="(*)"])
       apply simp
      apply (subst nn_integral_indicator)
      supply borel_open [measurable del] borel_closed [measurable del]
      using A'(2) K_def apply auto[1]
      apply (measurable, auto intro: phi_image_sets)[1]
      using Suc indep_vars_subset apply fastforce
      done
    also have "... = (\<Pi>\<^sub>M t \<in> {0..Suc n}. distr M borel (S t)) (phi (Suc n) ` Pi\<^sub>E {0..Suc n} A')"
      unfolding S_def apply (subst PiM_S_phi)
         apply simp_all
      using A'(2) apply force
      using Suc(2) apply (meson Suc_leD atLeastatMost_subset_iff indep_vars_subset le_refl)
      apply (subst PiM_S_phi)
      apply auto
      using A'(2) apply force
      using Suc(2) apply (meson Suc_leD atLeastatMost_subset_iff indep_vars_subset le_refl)
      apply (fact mult.commute)
      done
    finally show "emeasure (kernel_measure (PiK (Suc n) K) 0) A =
                  emeasure (Pi\<^sub>M {0..Suc n} (\<lambda>t. distr M borel (S t))) A"
      using A' by blast
  qed
qed

text \<open>Reproducing the Klenke proof\<close>

text \<open>for k: 1..n define the measurable bijection phi by 
 phi_k (x_1,...,x_k) = (x_1, ..., x_1 + ... + x_k) \<close>
thm phi.simps
text \<open> instead of (x_1,...,x_k) we have PiE {0..k} X \<close>
(* Evidently, borel = sigma_sets UNIV {phi n ` A | A. i \<in> {0..n} \<longrightarrow> A i \<in> sets borel}
   - This falls out of @{thm phi_measurable_isomorphic} *)


end
