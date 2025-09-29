theory Extras
  imports "HOL-Probability.Probability"
begin
lemma arg_cong3: "\<lbrakk>a = d; b = e; c = f\<rbrakk> \<Longrightarrow> g a b c = g d e f"
  by simp

lemma fun_upd_funcset_insert:
  assumes "f \<in> S \<rightarrow> R" "k \<in> R"
  shows "f(i := k) \<in> insert i S \<rightarrow> R"
  using assms by (simp add: Pi_iff)  

lemma indicator_PiE_fun_upd:
  assumes "i \<notin> S" "f i = undefined"
  shows "indicator (PiE (insert i S) F) (f (i:=a)) = indicator (PiE S F) f * (indicator (F i) a :: 'a :: linordered_semidom)"
  apply (simp split: split_indicator)
  using assms apply safe
       apply simp_all
      apply (meson PiE_E)
     apply (meson PiE_E)
    apply fastforce
   apply (metis PiE_restrict Pi_cancel_fupd Pi_mem Pi_split_insert_domain restrict_PiE)
  apply (metis PiE_arb fun_upd_other insertE)
  done

lemma finite_measure_return[simp]: "x \<in> space M \<Longrightarrow> finite_measure (return M x)"
  by (fact prob_space_return[THEN prob_space.finite_measure])

lemma countably_additive_cong:
  assumes "S = S'" "\<And>x. x \<in> S \<Longrightarrow> f x = f' x"
  shows "countably_additive S f = countably_additive S' f'"
proof -
  have "countably_additive X g \<Longrightarrow> countably_additive X h"
    if "\<And>x. x \<in> X \<Longrightarrow> h x = g x" for X :: "'a set set" and g h
    apply (auto intro!: countably_additiveI simp add: that countably_additive_def)
    apply (subst that)
    by blast+
  then show ?thesis
    using assms by metis
qed

lemma countably_additive_image:
  fixes S :: "'a \<Rightarrow> 'b"
  assumes "countably_additive M f"
    and inj: "inj_on S (\<Union> M)"
    and inv_into: "\<And>x. x \<in> (\<Union> ((`) S ` M)) \<Longrightarrow> S' x = inv_into (\<Union>M) S x"
  shows "countably_additive ((`) S ` M) (f \<circ> (`) S')"
proof (intro countably_additiveI)
  fix A :: "nat => 'b set"
  assume *: "range A \<subseteq> (`) S ` M" "disjoint_family A" "\<Union> (range A) \<in> (`) S ` M"
  have countably_additive: "\<And>A'. \<lbrakk>range A' \<subseteq> M; disjoint_family A'; \<Union> (range A') \<in> M\<rbrakk>
    \<Longrightarrow> (\<Sum>i. f (A' i)) = f (\<Union> (range A'))"
    using assms(1) countably_additive_def by blast
  have S'_image: "\<And>x. x \<in> ((`) S ` M) \<Longrightarrow> S' ` x = inv_into (\<Union>M) S ` x"
    by (meson inv_into UnionI image_cong)
  have "S' ` (A i) \<in> (`) S' ` (`) S ` M" for i
    using *(1) by fast
  moreover have "(`) S' ` (`) S ` M = M"
  proof (intro subset_antisym subsetI, goal_cases)
    case (1 X)
    then obtain x where "x \<in> M" "X = S' ` S ` x"
      by blast
    then show ?case
      by (simp add: S'_image Sup_upper assms(2))
  next
    case (2 x)
    then show ?case
      by (simp add: S'_image Sup_upper assms(2) image_iff)
  qed
  ultimately have "S' ` (A i) \<in> M" for i
    by simp
  then have "range ((`) S' \<circ> A) \<subseteq> M"
    by auto
  moreover have "disjoint_family ((`) S' \<circ> A)"
    unfolding disjoint_family_on_def
    apply (simp, safe)
    by (smt (verit) inv_into inj *(2,3) UNIV_I UnionI disjoint_family_onD equals0D f_inv_into_f
          image_Union mem_simps(4) rangeI)
  moreover have "\<Union> (range ((`) S' \<circ> A)) \<in> M"
    by (metis * (3) Inf.INF_image Set.basic_monos(1) \<open>(`) S' ` (`) S ` M = M\<close> image_Union image_subset_iff)
  ultimately have "(\<Sum>i. f (((`) S' \<circ> A) i)) = f (\<Union> (range ((`) S' \<circ> A)))"
    using countably_additive by blast
  then show "(\<Sum>i. (f \<circ> (`) S') (A i)) = (f \<circ> (`) S') (\<Union> (range A))"
    by (simp add: image_UN)
qed

corollary countably_additive_image':
  assumes "countably_additive M f" "inj_on S (\<Union> M)"
    and "\<And>x. x \<in> \<Union> M' \<Longrightarrow> S_inv x = (inv_into (\<Union>M) S) x" "M' = (`) S ` M"
    and "\<And>x. x \<in> M' \<Longrightarrow> S' x = S_inv ` x"
  shows "countably_additive M' (\<lambda>x. f (S' x))"
  apply (subst countably_additive_cong[where S'="((`) S ` M)"])
  prefer 3
    apply (rule countably_additive_image[OF assms(1-3)])
  using assms(4) apply blast
  apply (fact assms(4))
  using assms(5) comp_def apply auto
  done

lemma Un_sets [simp]: "\<Union> (sets M) = space M"
  by (simp add: Sup_le_iff Sup_upper equalityI sets.sets_into_space)

lemma sets_PiM_single_image: "sets (Pi\<^sub>M {i} (\<lambda>i. M)) = (`) (\<lambda>S. \<lambda>x\<in>{i}. S) ` sets M"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> sets (Pi\<^sub>M {i} (\<lambda>i. M))"
  moreover have "{Pi\<^sub>E {i} X |X. (\<forall>i. X i \<in> sets M) \<and> finite {i. X i \<noteq> space M}} = {Pi\<^sub>E {i} (\<lambda>_. x) |x. x \<in> sets M}"
    apply (rule Collect_cong)
    apply safe
     apply blast
    apply (rule_tac x="\<lambda>ix. if ix=i then x else space M" in exI)
    apply auto
    done
  ultimately have "x \<in> sigma_sets ({i} \<rightarrow>\<^sub>E space M) {Pi\<^sub>E {i} (\<lambda>_. x) |x. x \<in> sets M}"
    using sets_PiM_finite[of "{i}" "\<lambda>i. M"] by simp
  then show "x \<in> (`) (\<lambda>S. \<lambda>x\<in>{i}. S) ` sets M"
  proof (simp add: image_def, induct x rule: sigma_sets.induct)
    case (Basic a)
    then show ?case 
      apply (auto simp: image_def)
       apply (rule_tac x=x in bexI)
       apply safe
         apply (metis PiE_E singletonD singletonI)
        apply auto[1]
      apply argo
      done
  next
    case Empty
    then show ?case
      by blast
  next
    case (Compl a)
    then obtain x where "a = {y. \<exists>x\<in>x. y = (\<lambda>xa\<in>{i}. x)}" "x \<in> sets M"
      by blast
    then show ?case
      apply (rule_tac x="space M - x" in bexI)
       apply safe[1]
      apply simp
         apply (rule_tac x="x i" in bexI)
          apply fastforce
          apply fastforce
         apply auto[1]
        apply (meson restrict_apply singletonD)
       apply (metis (no_types, lifting) restrict_apply' singleton_iff)
      apply simp
      done
  next
    case (Union a)
    then obtain S where S: "a k = {y. \<exists>x\<in>S k. y = (\<lambda>_\<in>{i}. x)}" "S k \<in> sets M" for k
      by meson
    show ?case
      using S by (blast intro!: bexI[where x="\<Union> (range S)"])
  qed
next
  fix x assume "x \<in> (`) (\<lambda>S. \<lambda>x\<in>{i}. S) ` sets M"
  then obtain S where S: "S \<in> sets M" "x = (`) (\<lambda>S. \<lambda>x\<in>{i}. S) S"
    by blast
  then have "x = Pi\<^sub>E {i} (\<lambda>i. S)"
    unfolding S(2) PiE_over_singleton_iff by blast
  then show "x \<in> sets (Pi\<^sub>M {i} (\<lambda>i. M))" 
    using S(1) by simp
qed

lemma sets_PiM_single_image': "sets (PiM {i} M) = (`) (\<lambda>S. \<lambda>x\<in>{i}. S) ` sets (M i)"
  by (metis sets_PiM_cong sets_PiM_single_image singletonD)

lemma vimage_measurable2 [measurable]:
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M N" "g \<in> M \<rightarrow>\<^sub>M L" "A \<in> sets N" "B \<in> sets L"
  shows "f -` A \<inter> g -` B \<inter> space M \<in> sets M"
  by measurable

lemma (in product_sigma_finite) emeasure_PiM_insert:
  assumes "finite I" "i \<notin> I" "\<And>j. j \<in> insert i I \<Longrightarrow> X j \<in> M j"
  shows "emeasure (PiM (insert i I) M) (PiE (insert i I) X) =
         emeasure (M i) (X i) * emeasure (PiM I M) (PiE I X)"
  apply (subst emeasure_PiM)
  using assms apply (simp_all add: emeasure_PiM prod.insert_remove)
  done

corollary emeasure_PiM_Suc:
  assumes "\<And>i. i \<in> {0..Suc n} \<Longrightarrow> X i \<in> sets (M i)" "product_sigma_finite M"
  shows "emeasure (PiM {0..Suc n} M) (PiE {0..Suc n} X) =
         emeasure (M (Suc n)) (X (Suc n)) * emeasure (PiM {0..n} M) (PiE {0..n} X)"
  using product_sigma_finite.emeasure_PiM_insert[OF assms(2)]
        assms(1) atLeast0_atMost_Suc
  by fastforce 

lemma (in prob_space) indep_vars_sum':
  fixes X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b :: euclidean_space"
  assumes I: "finite I" "i \<notin> I" and indep: "indep_vars (\<lambda>_. borel) X (insert i I)"
  shows "indep_var borel (X i) borel (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
proof -
  have "indep_var
    borel ((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i}))
    borel ((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I))"
    using I by (intro indep_var_compose[OF indep_var_restrict[OF indep]] ) auto
  also have "((\<lambda>f. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) {i})) = X i"
    by auto
  also have "((\<lambda>f. \<Sum>i\<in>I. f i) \<circ> (\<lambda>\<omega>. restrict (\<lambda>i. X i \<omega>) I)) = (\<lambda>\<omega>. \<Sum>i\<in>I. X i \<omega>)"
    by (auto cong: rev_conj_cong)
  finally show ?thesis .
qed

lemma (in prob_space) indep_set_sym: "indep_set S T \<Longrightarrow> indep_set T S"
  apply (rule indep_setI)
    apply (simp_all add: indep_sets2_eq)
  apply (metis Groups.mult_ac(2) inf_commute)
  done

corollary (in prob_space) indep_var_sym: "indep_var m X n Y \<Longrightarrow> indep_var n Y m X"
  unfolding indep_var_eq using indep_set_sym by fast

end